import os
import requests
import time
import logging
import threading
import json
import sys
import queue
import pyodbc
import hmac
import hashlib
import urllib.parse
import select
import ssl
import socket
import signal
import zlib
import decimal
import uuid
import math
from enum import Enum
from collections import deque
from datetime import datetime, timedelta
from websocket import create_connection, WebSocketConnectionClosedException
from typing import List, Dict, Any, Set, Optional, Deque, Tuple
from flask import Flask, render_template, redirect, jsonify, request, session, url_for
from functools import wraps
from dotenv import load_dotenv

# Load environment variable
load_dotenv()
# Setup logging - HANYA KE FILE
root_logger = logging.getLogger()
root_logger.setLevel(logging.INFO)
# Hapus semua handler yang ada
for handler in root_logger.handlers[:]:
    root_logger.removeHandler(handler)

# Handler untuk menulis log ke file
file_handler = logging.FileHandler("futures_signal_detector.log", mode='w')
formatter = logging.Formatter("%(asctime)s [%(levelname)s] [%(threadName)s] %(message)s")
file_handler.setFormatter(formatter)
root_logger.addHandler(file_handler)

logger = logging.getLogger(__name__)

# Import Flask dan SocketIO tanpa monkey patching
from flask import Flask, render_template, redirect, jsonify, request
from flask_socketio import SocketIO, emit
import traceback

class OrderType(Enum):
    LIMIT = "LIMIT"
    MARKET = "MARKET"

class OrderSide(Enum):
    BUY = "BUY"
    SELL = "SELL"

class DecimalEncoder(json.JSONEncoder):
    """Custom JSON encoder untuk menangani objek Decimal"""
    def default(self, o):
        if isinstance(o, decimal.Decimal):
            return float(o)
        return super(DecimalEncoder, self).default(o)

def login_required(f):
    @wraps(f)
    def decorated_function(*args, **kwargs):
        if 'logged_in' not in session:
            return redirect(url_for('login_page'))
        return f(*args, **kwargs)
    return decorated_function


class SignalDetector:
    # --- Konfigurasi ---
    SYMBOL_LIST_FILE = "listsymbol.txt"
    INTERVAL = "15m"
    MAX_CONCURRENT_REQUESTS = 20
    MAX_SYMBOLS = 150
    ORDERBOOK_DEPTH_LEVEL = 100
    LIQ_HISTORY_WINDOW = 15  # Menit untuk perhitungan rata-rata likuidasi

    # --- URL Endpoint ---
    LIQUIDATION_WS_URL = "wss://fstream.binance.com/ws/!forceOrder@arr"
    BASE_WS_URL = "wss://fstream.binance.com/stream?streams="
    EXCHANGE_INFO_URL = "https://fapi.binance.com/fapi/v1/exchangeInfo"
    PREMIUM_INDEX_URL = "https://fapi.binance.com/fapi/v1/premiumIndex"
    OPEN_INTEREST_URL = "https://fapi.binance.com/fapi/v1/openInterest"
    DEPTH_URL = "https://fapi.binance.com/fapi/v1/depth"
    MARK_PRICE_WS_URL = "wss://fstream.binance.com/ws/!markPrice@arr"
    KLINE_URL = "https://fapi.binance.com/fapi/v1/klines"
    ACCOUNT_BALANCE_URL = "https://fapi.binance.com/fapi/v2/balance"
    SYMBOL_INFO_URL = "https://fapi.binance.com/fapi/v1/exchangeInfo"

    # Konfigurasi Database
    SQL_SERVER = os.getenv("SQL_SERVER")
    SQL_DATABASE = os.getenv("SQL_DATABASE")
    SQL_USERNAME = os.getenv("SQL_USERNAME")
    SQL_PASSWORD = os.getenv("SQL_PASSWORD")
    SQL_DRIVER = os.getenv("SQL_DRIVER", "{ODBC Driver 17 for SQL Server}")

    # Binance API Configuration
    BINANCE_API_KEY = os.getenv("BINANCE_API_KEY")
    BINANCE_API_SECRET = os.getenv("BINANCE_API_SECRET")

    def __init__(self):
        self.symbols: List[str] = []
        self.valid_symbols: Set[str] = set()
        self.shutdown_event = threading.Event()
        self.SIGNAL_DETECTION_INTERVAL = 2  # Dalam detik
        self.AUTOBOT_TRAILING_INTERVAL = 2
        self.data_lock = threading.Lock()
        self.symbol_info_cache: Dict[str, Dict] = {}  # Cache untuk info simbol

        self.liquidation_accumulator: Dict[str, Dict[str, float]] = {}
        self.volume_accumulator: Dict[str, Dict[str, float]] = {}
        self.order_books: Dict[str, Dict[str, Any]] = {}
        self.display_data: Dict[str, Dict[str, Any]] = {}

        # Struktur data untuk harga
        self.last_prices: Dict[str, float] = {}
        self.mark_prices: Dict[str, float] = {}

        # Menyimpan OI sebelumnya untuk perhitungan perubahan
        self.previous_oi: Dict[str, float] = {}

        # Menyimpan history likuidasi untuk perhitungan rata-rata
        self.liquidation_history: Dict[str, Deque[Tuple[datetime, float, float]]] = {}

        # === STRUKTUR DATA BARU UNTUK PENINGKATAN SINYAL ===
        self.price_history: Dict[str, Deque[Tuple[datetime, float]]] = {}
        self.funding_history: Dict[str, Deque[float]] = {}
        self.atr_values: Dict[str, float] = {}  # Menyimpan nilai ATR14 terkini

        # Data kline
        self.current_candle: Dict[str, Dict] = {}  # Data candle saat ini
        self.previous_candle: Dict[str, Dict] = {}  # Data candle sebelumnya

        self.liquidation_queue = queue.Queue()
        self.trade_queue = queue.Queue()
        self.depth_queue = queue.Queue()  # Queue untuk depth updates

        # Menyimpan sinyal dan skor terakhir
        self.last_signals: Dict[str, str] = {}  # {symbol: 'LONG'/'SHORT'/'HOLD'}
        self.current_scores: Dict[str, int] = {}  # {symbol: skor_terakhir}
        self.signal_lock = threading.Lock()

        self.request_semaphore = threading.Semaphore(self.MAX_CONCURRENT_REQUESTS)
        self.session = self._create_session()

        # Untuk menyimpan candle timestamp terakhir per simbol
        self.last_candle_timestamps: Dict[str, datetime] = {}

        # Untuk menyimpan burst threshold
        self.burst_thresholds: Dict[str, Dict[str, float]] = {}

        # Inisialisasi Flask dan Socket.IO dengan buffer yang lebih besar
        self.flask_app = Flask(__name__)
        self.flask_app.config['CORS_HEADERS'] = 'Content-Type'
        self.socketio = SocketIO(
            self.flask_app,
            async_mode='threading',  # PERBAIKAN: Ganti ke threading
            cors_allowed_origins="*",
            logger=False,  # Nonaktifkan logger Socket.IO
            engineio_logger=False,  # Nonaktifkan engineio logger
            max_http_buffer_size=50 * 1024 * 1024,  # 50MB (ditingkatkan)
            ping_interval=30,  # Ditingkatkan
            ping_timeout=120,   # Ditingkatkan
            compression_threshold=1024,  # Kompresi untuk payload besar
            json=json  # Gunakan JSON encoder kustom
        )

        # Setup route
        self.flask_app.add_url_rule('/', 'dashboard', self.dashboard)
        self.flask_app.add_url_rule('/dashboard.html', 'index_redirect', self.index_redirect)
        self.flask_app.add_url_rule('/reload', 'manual_reload', self.manual_reload, methods=['POST'])
        self.flask_app.add_url_rule('/health', 'health_check', self.health_check)
        self.flask_app.add_url_rule('/symbol_info', 'symbol_info', self.symbol_info)
        self.flask_app.add_url_rule('/account_balance', 'account_balance', self.account_balance)
        self.flask_app.add_url_rule('/api/submit_order', 'submit_order', self.submit_order, methods=['POST'])
        # Tambahkan route untuk halaman open orders
        self.flask_app.add_url_rule('/open_orders.html', 'open_orders', self.open_orders_page)
        self.flask_app.add_url_rule('/api/open_orders', 'api_open_orders', self.get_open_orders)

        # Setup Socket.IO event
        self.socketio.on_event('connect', self.handle_connect, namespace='/')
        self.socketio.on_event('request_data', self.handle_request_data, namespace='/')
        self.socketio.on_event('disconnect', self.handle_disconnect, namespace='/')
        self.socketio.on_event('error', self.handle_error, namespace='/')

        # Data untuk dikirim ke klien
        self.client_data = {}
        self.last_update_time = datetime.utcnow()
        self.last_db_reload = time.time()
        self.last_emit_time = time.time()
        self.pending_price_updates = {}
        self.cached_formatted_data = None  # Cache untuk data yang diformat

        # Cache untuk data sinyal dari database
        self.signal_data_cache: Dict[str, Dict] = {}
        self.signal_cache_lock = threading.Lock()

        # Error counter
        self.error_counter = 0
        self.last_error_time = 0

        # Database connection semaphore and retry settings
        self.db_semaphore = threading.Semaphore(5)  # Batasi koneksi database simultan
        self.db_retry_attempts = 3
        self.db_retry_delay = 1  # detik

        # Cache untuk burst thresholds
        self.burst_threshold_cache: Dict[str, Tuple[Dict, float]] = {}
        self.burst_cache_lock = threading.Lock()

        # Cache untuk ATR values
        self.atr_cache: Dict[str, Tuple[float, float]] = {}
        self.atr_cache_lock = threading.Lock()
        self.atr_cache_timeout = 300  # 5 menit
        self.btc_price_index = 0.0
        self.btc_index_last_updated = datetime.min
        self.btc_recomendasi_btc = None

        # Cache untuk informasi simbol (minQty, minNotional)
        self.symbol_info_map: Dict[str, Dict] = {}
        self.symbol_info_cache_time = 0
        self.symbol_info_refresh_interval = 3600  # 1 jam

        # Cache untuk saldo akun
        self.account_balance_cache: Dict[str, float] = {}
        self.balance_cache_time = 0
        self.balance_refresh_interval = 30  # 1 menit

        self.open_orders_cache = None  # Cache untuk data open orders
        self.open_orders_last_updated = 0  # Timestamp terakhir update
        self.open_orders_lock = threading.Lock()  # Lock untuk akses cache
        self.flask_app.add_url_rule('/api/close_order', 'close_order', self.close_order, methods=['POST'])
        # Konfigurasi Auto Close berdasarkan PnL
        self.flask_app.add_url_rule('/api/cancel_order', 'cancel_order', self.cancel_order, methods=['POST'])
        self.AUTO_CLOSE_THRESHOLD_LOSS = -1.00  # USD
        self.AUTOBOT_MIN_TARGET_PROFIT = 1.4   # 0.25% profit minimal
        self.AUTOBOT_TRAILING_DISTANCE = 0.5   # 0.05% trailing distance
        self.autobot_trailing_stops = {}  # {order_id: {'max_profit': float, 'open_price': float}}
        self.auto_close_lock = threading.Lock()
        self.orders_in_process = set()  # Untuk melacak order yang sedang diproses

        self.flask_app.add_url_rule('/login', 'login_page', self.login_page, methods=['GET'])
        self.flask_app.add_url_rule('/login', 'login', self.login, methods=['POST'])
        self.flask_app.add_url_rule('/logout', 'logout', self.logout)
        self.flask_app.secret_key = os.getenv("FLASK_SECRET_KEY", "default_secret_key")
        self.flask_app.add_url_rule('/check_auth', 'check_auth', self.check_auth)

        #autobot
        self.autobot_enabled = False
        self.flask_app.add_url_rule('/api/autobot_status', 'autobot_status', self.get_autobot_status)
        self.flask_app.add_url_rule('/api/toggle_autobot', 'toggle_autobot', self.toggle_autobot, methods=['POST'])

        # Cache untuk melacak candle terakhir di mana autobot telah membuka posisi
        self.autobot_last_open: Dict[str, datetime] = {}

    # ========== FUNGSI INDIKATOR DINONAKTIFKAN ==========
    # Semua fungsi terkait indikator dihapus/disable
    
    # --- PERBAIKAN: Fungsi baru untuk memformat nilai sesuai aturan presisi Binance ---
    def _format_value(self, value: float, step_or_tick_size: str) -> str:
        """
        Memformat sebuah nilai (kuantitas atau harga) agar sesuai dengan aturan step/tick size.
        Ini akan membulatkan nilai KE BAWAH ke kelipatan terdekat dari step/tick size.
        """
        try:
            # Menggunakan Decimal untuk presisi tinggi
            value_decimal = decimal.Decimal(str(value))
            step_decimal = decimal.Decimal(step_or_tick_size)
            
            # quantize adalah cara yang benar untuk membulatkan ke kelipatan tertentu
            # rounding=decimal.ROUND_DOWN memastikan kita tidak melebihi batas (misal. saldo)
            formatted_value = value_decimal.quantize(step_decimal, rounding=decimal.ROUND_DOWN)
            
            # Mengembalikan sebagai string, sesuai yang diharapkan API Binance
            return str(formatted_value)
        except (decimal.InvalidOperation, TypeError):
            # Fallback jika ada error, meskipun seharusnya tidak terjadi
            logger.error(f"Gagal memformat nilai {value} dengan step/tick {step_or_tick_size}")
            return str(value)


    @login_required
    def get_autobot_status(self):
        return jsonify({
            'status': 'success',
            'autobot_enabled': self.autobot_enabled
        })

    @login_required
    def toggle_autobot(self):
        try:
            self.autobot_enabled = not self.autobot_enabled
            # Broadcast new status to all clients
            self.socketio.emit('autobot_status',
                              {'enabled': self.autobot_enabled},
                              namespace='/')
            return jsonify({
                'success': True,
                'enabled': self.autobot_enabled
            })
        except Exception as e:
            logger.error(f"Error toggling autobot: {e}")
            return jsonify({'success': False, 'error': str(e)}), 500

    def _autobot_open_position(self, symbol: str, position: str, mark_price: float, current_candle: datetime):

        if mark_price > 50.0:
            logger.info(f"Autobot: Skip open position for {symbol} (price ${mark_price:.2f} > $50)")
            return False

        if not self.autobot_enabled:
            return False

        # Cek apakah sudah ada posisi dalam 2 interval terakhir (30 menit)
        last_open = self.autobot_last_open.get(symbol)
        if last_open:
            # Hitung selisih waktu antara candle saat ini dan candle terakhir pembukaan
            time_diff = (current_candle - last_open).total_seconds()  # dalam detik
            if time_diff < 1800:  # 30 menit * 60 detik
                logger.info(f"Autobot: Posisi untuk {symbol} sudah dibuka dalam 30 menit terakhir. Melewati.")
                return False

        # Dapatkan info simbol yang sudah di-cache
        symbol_info = self.symbol_info_map.get(symbol)
        if not symbol_info:
            logger.error(f"Autobot: Info simbol untuk {symbol} tidak ditemukan. Perlu refresh data.")
            self._fetch_symbol_info_map() # Coba ambil lagi
            symbol_info = self.symbol_info_map.get(symbol)
            if not symbol_info:
                logger.error(f"Autobot: Info simbol untuk {symbol} tetap tidak ditemukan. Melewati.")
                return False

        # --- Logika Perhitungan Kuantitas yang Diperbaiki ---
        notional = 55.0  # Target notional 100 USDT
        initial_quantity = notional / mark_price

        min_qty = symbol_info.get('minQty', 0.0)
        step_size = symbol_info.get('stepSize', 0.0)
        min_notional = symbol_info.get('minNotional', 0.0)
        tick_size = symbol_info.get('tickSize', 0.0)  # PERLU DITAMBAHKAN

        logger.info(f"Autobot [{symbol}]: Info -> StepSize: {step_size}, MinQty: {min_qty}, MinNotional: {min_notional}, TickSize: {tick_size}")
        logger.info(f"Autobot [{symbol}]: Kuantitas awal (dari notional $100) = {initial_quantity}")

        # 1. Pastikan notional terpenuhi
        if notional < min_notional:
            logger.warning(f"Autobot [{symbol}]: Notional $100 di bawah minimum ${min_notional}. Menyesuaikan notional.")
            notional = min_notional * 1.05 # Gunakan sedikit di atas minimum
            initial_quantity = notional / mark_price
            logger.info(f"Autobot [{symbol}]: Kuantitas disesuaikan untuk minNotional = {initial_quantity}")

        # 2. Sesuaikan kuantitas dengan stepSize (ATURAN PALING PENTING)
        if step_size > 0:
            # Gunakan floor division untuk memastikan kuantitas adalah kelipatan dari step_size
            adjusted_quantity = math.floor(initial_quantity / step_size) * step_size

            # Bulatkan ke presisi yang benar untuk menghilangkan sisa floating point
            precision = self._get_step_precision(step_size)
            final_quantity = round(adjusted_quantity, precision)
            logger.info(f"Autobot [{symbol}]: Kuantitas setelah penyesuaian stepSize = {final_quantity}")
        else:
            final_quantity = round(initial_quantity, 8) # Fallback jika step_size tidak ada
            logger.warning(f"Autobot [{symbol}]: Step size 0, menggunakan pembulatan standar: {final_quantity}")

        # 3. Validasi akhir terhadap minQty dan minNotional
        if final_quantity < min_qty:
            logger.warning(f"Autobot [{symbol}]: Kuantitas {final_quantity} < MinQty {min_qty}. Menaikkan ke MinQty.")
            final_quantity = min_qty

        if (final_quantity * mark_price) < min_notional:
            logger.error(f"Autobot [{symbol}]: Notional akhir (${final_quantity * mark_price}) < MinNotional (${min_notional}). Gagal membuat order.")
            return False

        # Tentukan side
        side = OrderSide.BUY if position == 'LONG' else OrderSide.SELL
        posisi_db = 'LONG' if position == 'LONG' else 'SHORT'

        # Set leverage
        try:
            self._set_leverage(symbol, 50)
        except Exception as e:
            logger.error(f"Autobot [{symbol}]: Gagal mengatur leverage: {e}")
            return False

        # Hitung harga entry berdasarkan posisi
        if position == 'LONG':
            # LONG: harga pasar - 0.1%
            entry_price = mark_price * 0.99999
        else:
            # SHORT: harga pasar + 0.1%
            entry_price = mark_price * 1.00001

        # Sesuaikan dengan tick size
        if tick_size > 0:
            # Hitung berapa langkah dari tick size
            steps = round(entry_price / tick_size)
            entry_price = steps * tick_size
            # Bulatkan ke presisi yang sesuai
            precision = self._get_step_precision(tick_size)
            entry_price = round(entry_price, precision)
            logger.info(f"Autobot [{symbol}]: Harga entry disesuaikan dengan tickSize: {entry_price}")

        # Place the LIMIT order
        logger.info(f"Autobot: Menempatkan order {position} LIMIT untuk {symbol}, Qty: {final_quantity}, Harga: {entry_price:.6f}, Notional: ${final_quantity * entry_price:.2f}")
        order_result = self._place_binance_order(
            symbol=symbol,
            side=side,
            order_type=OrderType.LIMIT,  # UBAH KE LIMIT
            quantity=str(final_quantity), # Kirim sebagai string
            price=str(entry_price)  # Kirim sebagai string
        )

        if not order_result.get('success'):
            error_msg = order_result.get('msg', 'Unknown error')
            logger.error(f"Autobot: Gagal membuat order untuk {symbol}: {error_msg}")
            return False

        # --- Lanjutan proses penyimpanan ke DB ---
        binance_order_id = order_result['data'].get('orderId')
        if not binance_order_id:
            logger.error("Autobot: Tidak ada order ID dalam respons Binance.")
            return False

        db_success = self._submit_order_to_database(
            symbol=symbol, side=posisi_db, order_type=OrderType.LIMIT.value,  # UBAH KE LIMIT
            quantity=final_quantity, price=entry_price, leverage=50,  # GUNAKAN HARGA ENTRY
            stop_loss=None, take_profit=None,
            binance_order_id=str(binance_order_id), initial=True
        )

        if db_success:
            logger.info(f"Autobot: Order untuk {symbol} berhasil disimpan ke database. ID: {binance_order_id}")
            self.autobot_last_open[symbol] = current_candle

            # Mulai trailing stop monitoring
            self.autobot_trailing_stops[binance_order_id] = {
                'max_profit': 0.0,
                'open_price': mark_price,
                'symbol': symbol,
                'position': position,
                'quantity': final_quantity
            }

            threading.Thread(
                target=self._monitor_trailing_stop,
                args=(binance_order_id,),
                daemon=True
            ).start()
            return True
        else:
            logger.error(f"Autobot: Order {binance_order_id} berhasil di Binance tetapi GAGAL disimpan ke database.")
            return False

    def _monitor_trailing_stop(self, binance_order_id: str):
        """Thread untuk memantau trailing stop autobot dalam USD"""
        logger.info(f"Memulai trailing stop monitor untuk order {binance_order_id}")

        while not self.shutdown_event.is_set():
            try:
                time.sleep(self.AUTOBOT_TRAILING_INTERVAL)  # Perpendek interval menjadi 1 detik

                # Dapatkan data trailing stop
                with self.auto_close_lock:
                    if binance_order_id not in self.autobot_trailing_stops:
                        break

                    trail_data = self.autobot_trailing_stops[binance_order_id]
                    symbol = trail_data['symbol']
                    position = trail_data['position']
                    open_price = trail_data['open_price']
                    quantity = trail_data['quantity']
                    max_profit = trail_data['max_profit']

                # Dapatkan harga mark terbaru
                with self.data_lock:
                    mark_price = self.mark_prices.get(symbol, 0.0)

                if mark_price == 0.0:
                    continue # Skip jika harga tidak tersedia

                # Hitung profit saat ini (dalam USD)
                if position == 'LONG':
                    current_profit = (mark_price - open_price) * quantity
                else: # SHORT
                    current_profit = (open_price - mark_price) * quantity

                # Jika mencapai target minimum, mulai trailing
                if current_profit >= self.AUTOBOT_MIN_TARGET_PROFIT:
                    # Update profit maksimum jika melebihi
                    if current_profit > max_profit:
                        with self.auto_close_lock:
                            # Pastikan order masih ada sebelum update
                            if binance_order_id in self.autobot_trailing_stops:
                                self.autobot_trailing_stops[binance_order_id]['max_profit'] = current_profit
                                max_profit = current_profit
                        # logger.info(f"Trailing stop: Profit baru ${max_profit:.4f} untuk {binance_order_id}")

                    # Cek apakah turun dari max profit melebihi trailing distance (USD)
                    if current_profit <= (max_profit - self.AUTOBOT_TRAILING_DISTANCE):
                        logger.info(f"Trailing stop dipicu! Menutup posisi {binance_order_id}")
                        self._close_autobot_position(binance_order_id, mark_price)
                        break # Hentikan loop setelah menutup posisi

                # PERBAIKAN: Tambahkan logika jika profit di bawah minimum
                elif current_profit < self.AUTOBOT_MIN_TARGET_PROFIT and max_profit > 0:
                    # Reset max profit jika profit turun di bawah minimum
                    with self.auto_close_lock:
                        if binance_order_id in self.autobot_trailing_stops:
                           self.autobot_trailing_stops[binance_order_id]['max_profit'] = 0.0


            except KeyError:
                logger.warning(f"Order {binance_order_id} tidak lagi di trailing stops. Mungkin sudah ditutup.")
                break
            except Exception as e:
                logger.error(f"Error dalam monitor trailing stop untuk {binance_order_id}: {e}")
                time.sleep(10) # Tunggu lebih lama jika ada error

        # Hapus dari tracking setelah loop selesai
        with self.auto_close_lock:
            if binance_order_id in self.autobot_trailing_stops:
                del self.autobot_trailing_stops[binance_order_id]
        logger.info(f"Trailing stop dihentikan untuk order {binance_order_id}")


    def _close_autobot_position(self, binance_order_id: str, current_price: float):
        """Tutup posisi autobot berdasarkan trailing stop"""
        try:
            # Hapus dari daftar trailing SEBELUM mencoba menutup
            with self.auto_close_lock:
                if binance_order_id not in self.autobot_trailing_stops:
                    logger.warning(f"Autobot: Mencoba menutup order {binance_order_id} yang tidak ada di trailing stop.")
                    return False
                trail_data = self.autobot_trailing_stops.pop(binance_order_id)

            symbol = trail_data['symbol']
            position = trail_data['position']
            quantity = trail_data['quantity']

            # Tentukan sisi untuk menutup posisi
            close_side = OrderSide.SELL if position == 'LONG' else OrderSide.BUY

            logger.info(f"Autobot: Menutup posisi {position} untuk {symbol} sejumlah {quantity}")

            # Gunakan _place_binance_order untuk menutup dengan MARKET order
            close_result = self._place_binance_order(
                symbol=symbol,
                side=close_side,
                order_type=OrderType.MARKET,
                quantity=str(quantity),
                reduce_only=True # Parameter penting untuk hanya menutup posisi
            )

            if close_result.get('success'):
                # Dapatkan harga eksekusi dari respons (jika ada)
                # Note: Untuk market order, harga eksekusi ada di 'avgPrice' atau perlu di-query lagi
                # Untuk penyederhanaan, kita akan update status saja
                closed_order_id = close_result['data'].get('orderId')
                logger.info(f"Autobot: Posisi {binance_order_id} berhasil ditutup dengan order baru {closed_order_id}.")

                # Ambil detail order yang ditutup untuk mendapatkan harga rata-rata
                time.sleep(1) # Beri jeda agar order terisi
                closed_order_detail = self._fetch_binance_order_detail(closed_order_id, symbol)
                close_price = float(closed_order_detail.get('avgPrice', current_price))


                # Update database
                update_success = self._update_order_status_by_binance_id(
                    binance_order_id=str(binance_order_id),
                    status=0, # 0 = CLOSED
                    close_price=close_price
                )
                if update_success:
                    logger.info(f"Autobot: Status order {binance_order_id} di database berhasil diupdate.")
                else:
                    logger.error(f"Autobot: GAGAL mengupdate status order {binance_order_id} di database.")

                return True
            else:
                error_msg = close_result.get('msg', 'Unknown error')
                logger.error(f"Autobot: Gagal menutup posisi {binance_order_id} di Binance: {error_msg}")
                 # Jika gagal, tambahkan kembali ke daftar trailing agar bisa dicoba lagi
                with self.auto_close_lock:
                    self.autobot_trailing_stops[binance_order_id] = trail_data
                return False

        except Exception as e:
            logger.error(f"Error saat menutup posisi autobot {binance_order_id}: {e}")
            # Jika gagal karena error tak terduga, coba tambahkan kembali
            if 'trail_data' in locals():
                 with self.auto_close_lock:
                    self.autobot_trailing_stops[binance_order_id] = trail_data
            return False


    def _set_leverage(self, symbol: str, leverage: int):
        """Helper function to set leverage for a symbol."""
        set_leverage_url = "https://fapi.binance.com/fapi/v1/leverage"
        params = {
            'symbol': symbol,
            'leverage': leverage,
            'timestamp': int(time.time() * 1000)
        }
        params['signature'] = self._generate_signature(params)
        try:
            response = requests.post(
                set_leverage_url,
                params=params,
                headers={"X-MBX-APIKEY": self.BINANCE_API_KEY},
                timeout=5
            )
            response.raise_for_status() # Akan raise exception jika gagal
            logger.info(f"Autobot: Leverage untuk {symbol} diatur ke {leverage}x.")
            return True
        except requests.exceptions.RequestException as e:
            logger.error(f"Error mengatur leverage untuk {symbol}: {e.response.text if e.response else e}")
            return False


    def _sync_order_price(self, binance_order_id: str, symbol: str):
        """Sinkronisasi harga order dengan Binance"""
        attempts = 0
        max_attempts = 10
        order_filled = False
        while attempts < max_attempts and not self.shutdown_event.is_set():
            attempts += 1
            time.sleep(3)  # Tunggu 3 detik antar percobaan
            try:
                order_detail = self._fetch_binance_order_detail(
                    int(binance_order_id), symbol
                )

                if not order_detail:
                    continue

                status = order_detail.get('status')

                # Handle filled orders
                if status in ['PARTIALLY_FILLED', 'FILLED']:
                    executed_qty = float(order_detail.get('executedQty', 0))
                    if executed_qty > 0:
                        executed_price = float(order_detail.get('avgPrice', 0))

                        # Update harga pembukaan di trailing stop
                        with self.auto_close_lock:
                            if binance_order_id in self.autobot_trailing_stops:
                                self.autobot_trailing_stops[binance_order_id]['open_price'] = executed_price

                        # Update database dengan harga sebenarnya
                        update_success = self._update_order_price_by_binance_id(
                            binance_order_id, executed_price
                        )

                        if update_success:
                            logger.info(f"Autobot: Successfully synced price for order {binance_order_id} @ {executed_price}")
                        else:
                            logger.warning(f"Autobot: Failed to update price for order {binance_order_id}")

                        order_filled = True
                        break

                elif status in ['CANCELED', 'EXPIRED']:
                    logger.warning(f"Autobot: Order {binance_order_id} dibatalkan atau kedaluwarsa. Menghentikan trailing.")
                    with self.auto_close_lock:
                        if binance_order_id in self.autobot_trailing_stops:
                            del self.autobot_trailing_stops[binance_order_id]
                    break

            except Exception as e:
                logger.error(f"Error syncing order price for {binance_order_id}: {e}")

        if not order_filled:
            logger.error(f"Autobot: Gagal menyinkronkan harga untuk order {binance_order_id} setelah {max_attempts} percobaan.")


    def login_page(self):
        return render_template('login.html')

    def login(self):
        # Kata sandi yang benar (sebaiknya disimpan di environment variable)
        CORRECT_PASSWORD = os.getenv("WEB_PASSWORD", "default_password")

        if request.form.get('password') == CORRECT_PASSWORD:
            session['logged_in'] = True
            return redirect(url_for('dashboard'))
        else:
            return render_template('login.html', error="Password salah!")

    @login_required
    def logout(self):
        session.pop('logged_in', None)
        return redirect(url_for('login_page'))

    @login_required
    def check_auth(self):
        return jsonify({'logged_in': True})


    # --- Fungsi Utama ---
    def _create_session(self) -> requests.Session:
        session = requests.Session()
        adapter = requests.adapters.HTTPAdapter(pool_connections=50, pool_maxsize=50)
        session.mount('https://', adapter)
        return session

    def _get_db_connection(self):
        """Mendapatkan koneksi database dengan semaphore dan retry."""
        with self.db_semaphore:
            for attempt in range(self.db_retry_attempts):
                try:
                    cnxn = pyodbc.connect(
                        f'DRIVER={self.SQL_DRIVER};'
                        f'SERVER={self.SQL_SERVER};'
                        f'DATABASE={self.SQL_DATABASE};'
                        f'UID={self.SQL_USERNAME};'
                        f'PWD={self.SQL_PASSWORD};'
                        'TrustServerCertificate=yes;'
                        'Connection Timeout=30;' # Timeout koneksi
                    )
                    return cnxn
                except pyodbc.Error as ex:
                    sqlstate = ex.args[0]
                    logger.error(f"Database connection error (attempt {attempt + 1}/{self.db_retry_attempts}): {sqlstate} - {ex}")
                    if attempt < self.db_retry_attempts - 1:
                        time.sleep(self.db_retry_delay)
                    else:
                        raise  # Raise the exception after the last attempt

    def load_symbols(self):
        try:
            with open(self.SYMBOL_LIST_FILE, "r") as f:
                self.symbols = [line.strip().upper() for line in f if line.strip() and not line.startswith("#")]
                self.symbols = self.symbols[:self.MAX_SYMBOLS]
            logger.info(f"Loaded {len(self.symbols)} symbols from {self.SYMBOL_LIST_FILE}.")
        except FileNotFoundError:
            logger.error(f"Symbol list file not found: {self.SYMBOL_LIST_FILE}. Exiting.")
            sys.exit(1)

    def _fetch_exchange_info(self):
        """Mengambil informasi exchange dan memfilter simbol yang valid."""
        try:
            response = self.session.get(self.EXCHANGE_INFO_URL, timeout=10)
            response.raise_for_status()
            data = response.json()
            valid_api_symbols = {
                s['symbol'] for s in data['symbols']
                if s['status'] == 'TRADING' and s['contractType'] == 'PERPETUAL'
            }
            self.valid_symbols = set(self.symbols) & valid_api_symbols
            logger.info(f"Validated {len(self.valid_symbols)} symbols against exchange info.")

            # PERBAIKAN: Isi cache symbol_info_cache di sini
            for s in data['symbols']:
                if s['symbol'] in self.valid_symbols:
                    self.symbol_info_cache[s['symbol']] = s

        except requests.RequestException as e:
            logger.error(f"Error fetching exchange info: {e}. Using pre-loaded symbol list.")
            self.valid_symbols = set(self.symbols) # Fallback

    def _get_step_precision(self, step_size_str: str) -> int:
        """Menghitung jumlah desimal dari step size."""
        # Menggunakan Decimal untuk akurasi
        step_decimal = decimal.Decimal(step_size_str)
        # 'as_tuple().exponent' memberikan jumlah tempat desimal sebagai bilangan negatif
        return abs(step_decimal.as_tuple().exponent)


    def _fetch_symbol_info_map(self):
        """Mengambil dan mem-cache informasi penting (minQty, stepSize, minNotional) untuk semua simbol valid."""
        current_time = time.time()
        # Cek apakah cache masih valid
        if self.symbol_info_map and (current_time - self.symbol_info_cache_time) < self.symbol_info_refresh_interval:
            return

        logger.info("Refreshing symbol info map (minQty, stepSize, minNotional)...")
        try:
            response = self.session.get(self.SYMBOL_INFO_URL, timeout=10)
            response.raise_for_status()
            data = response.json()
            temp_map = {}
            for s in data['symbols']:
                if s['symbol'] in self.valid_symbols:
                    # Cari filter LOT_SIZE dan MIN_NOTIONAL
                    lot_size_filter = next((f for f in s['filters'] if f['filterType'] == 'LOT_SIZE'), None)
                    min_notional_filter = next((f for f in s['filters'] if f['filterType'] == 'MIN_NOTIONAL'), None)
                    price_filter = next((f for f in s['filters'] if f['filterType'] == 'PRICE_FILTER'), None)


                    if lot_size_filter and min_notional_filter and price_filter:
                         temp_map[s['symbol']] = {
                            'minQty': float(lot_size_filter['minQty']),
                            'stepSize': float(lot_size_filter['stepSize']),
                            'minNotional': float(min_notional_filter['notional']),
                            'tickSize': float(price_filter['tickSize']) # Tambahkan tickSize
                        }

            self.symbol_info_map = temp_map
            self.symbol_info_cache_time = current_time # Update timestamp cache
            logger.info(f"Successfully refreshed and cached info for {len(self.symbol_info_map)} symbols.")

        except requests.RequestException as e:
            logger.error(f"Error fetching detailed symbol info: {e}")
        except Exception as e:
            logger.error(f"An unexpected error occurred in _fetch_symbol_info_map: {e}")


    def _initialize_data(self):
        """Mengambil data awal (OI, Premium Index, Order Book) untuk semua simbol."""
        logger.info("Initializing data for all symbols...")
        threads = []
        for symbol in self.valid_symbols:
            # Inisialisasi struktur data
            with self.data_lock:
                self.display_data[symbol] = {'symbol': symbol}
                self.liquidation_accumulator[symbol] = {'buy': 0, 'sell': 0}
                self.volume_accumulator[symbol] = {'buy': 0, 'sell': 0}
                self.order_books[symbol] = {'bids': {}, 'asks': {}}
                self.liquidation_history[symbol] = deque(maxlen=self.LIQ_HISTORY_WINDOW * 60) # simpan per detik
                self.price_history[symbol] = deque(maxlen=20) # History harga untuk deteksi spike
                self.funding_history[symbol] = deque(maxlen=10)

            # Thread untuk mengambil data awal
            thread = threading.Thread(target=self._fetch_initial_symbol_data, args=(symbol,), daemon=True)
            threads.append(thread)
            thread.start()

        for thread in threads:
            thread.join()
        logger.info("Initial data fetch complete.")

    def _fetch_initial_symbol_data(self, symbol: str):
        """Mengambil data awal untuk satu simbol."""
        with self.request_semaphore:
            try:
                # Ambil Open Interest
                oi_res = self.session.get(self.OPEN_INTEREST_URL, params={'symbol': symbol}, timeout=5)
                oi_res.raise_for_status()
                oi_data = oi_res.json()
                with self.data_lock:
                    self.display_data[symbol]['open_interest'] = float(oi_data['openInterest'])
                    self.previous_oi[symbol] = float(oi_data['openInterest'])

                # Ambil Premium Index (termasuk mark price dan funding rate)
                pi_res = self.session.get(self.PREMIUM_INDEX_URL, params={'symbol': symbol}, timeout=5)
                pi_res.raise_for_status()
                pi_data = pi_res.json()
                with self.data_lock:
                    self.display_data[symbol]['funding_rate'] = float(pi_data['lastFundingRate']) * 100
                    self.mark_prices[symbol] = float(pi_data['markPrice'])

                # Ambil Order Book Depth
                depth_res = self.session.get(self.DEPTH_URL, params={'symbol': symbol, 'limit': self.ORDERBOOK_DEPTH_LEVEL}, timeout=5)
                depth_res.raise_for_status()
                depth_data = depth_res.json()
                with self.data_lock:
                    bids = {float(p): float(q) for p, q in depth_data['bids']}
                    asks = {float(p): float(q) for p, q in depth_data['asks']}
                    self.order_books[symbol] = {'bids': bids, 'asks': asks}

            except requests.RequestException as e:
                logger.warning(f"Failed to fetch initial data for {symbol}: {e}")
            except Exception as e:
                logger.error(f"Unexpected error fetching initial data for {symbol}: {e}")

    # --- WebSocket Handling ---
    def _get_websocket_streams(self) -> List[str]:
        """Membuat daftar stream untuk koneksi WebSocket."""
        streams = []
        for symbol in self.valid_symbols:
            streams.append(f"{symbol.lower()}@aggTrade")
            streams.append(f"{symbol.lower()}@depth")
            streams.append(f"{symbol.lower()}@kline_{self.INTERVAL}")
        return streams

    def _connect_websocket(self, url: str) -> any:
        """Menghubungkan ke WebSocket dengan penanganan error dan retry."""
        while not self.shutdown_event.is_set():
            try:
                logger.info(f"Connecting to WebSocket: {url[:100]}...")
                # Tambahkan timeout ke create_connection
                ws = create_connection(url, timeout=30,
                                       sslopt={"cert_reqs": ssl.CERT_NONE}) # Opsi untuk development
                logger.info("WebSocket connection successful.")
                return ws
            except (WebSocketConnectionClosedException, ConnectionRefusedError, socket.timeout, OSError) as e:
                logger.error(f"WebSocket connection failed: {e}. Retrying in 10 seconds...")
                time.sleep(10)
            except Exception as e:
                logger.error(f"An unexpected error occurred during WebSocket connection: {e}. Retrying in 10 seconds...")
                time.sleep(10)
        return None


    def _websocket_thread_func(self, streams: List[str]):
        """Thread untuk menangani stream data utama dari WebSocket."""
        url = self.BASE_WS_URL + "/".join(streams)
        ws = self._connect_websocket(url)
        if not ws: return

        while not self.shutdown_event.is_set():
            try:
                # Gunakan select untuk non-blocking read dengan timeout
                ready_to_read, _, _ = select.select([ws.sock], [], [], 1.0)
                if not ready_to_read:
                    # Timeout, kirim ping untuk menjaga koneksi
                    try:
                        ws.ping()
                    except Exception as ping_err:
                         logger.warning(f"Failed to send ping: {ping_err}. Reconnecting...")
                         raise WebSocketConnectionClosedException("Ping failed")
                    continue

                # Decompress pesan jika perlu (untuk koneksi wss://fstream.binance.com)
                raw_message = ws.recv()
                message = json.loads(raw_message)

                if 'stream' in message and 'data' in message:
                    stream_name = message['stream']
                    data = message['data']
                    symbol = data.get('s', '').upper()

                    if not symbol or symbol not in self.valid_symbols:
                        continue

                    event_type = data.get('e')
                    if event_type == 'aggTrade':
                        self._process_trade_data(data)
                    elif event_type == 'depthUpdate':
                        self.depth_queue.put(data) # Masukkan ke queue
                    elif event_type == 'kline':
                        self._process_kline_data(data)

            except (WebSocketConnectionClosedException, json.JSONDecodeError, AttributeError, socket.timeout, OSError) as e:
                logger.error(f"WebSocket error in main stream: {e}. Reconnecting...")
                ws.close()
                ws = self._connect_websocket(url)
                if not ws: break
            except Exception as e:
                logger.error(f"An unexpected error in main WebSocket thread: {e}", exc_info=True)
                time.sleep(5) # Jeda singkat sebelum melanjutkan


    def _liquidation_ws_thread_func(self):
        """Thread untuk menangani stream data likuidasi."""
        ws = self._connect_websocket(self.LIQUIDATION_WS_URL)
        if not ws: return

        while not self.shutdown_event.is_set():
            try:
                 # Gunakan select untuk non-blocking read dengan timeout
                ready_to_read, _, _ = select.select([ws.sock], [], [], 1.0)
                if not ready_to_read:
                    try:
                        ws.ping()
                    except Exception as ping_err:
                         logger.warning(f"Failed to send ping on liquidation stream: {ping_err}. Reconnecting...")
                         raise WebSocketConnectionClosedException("Ping failed")
                    continue

                message = json.loads(ws.recv())
                if 'o' in message:
                    self._process_liquidation_data(message['o'])

            except (WebSocketConnectionClosedException, json.JSONDecodeError, AttributeError, socket.timeout, OSError) as e:
                logger.error(f"WebSocket error in liquidation stream: {e}. Reconnecting...")
                ws.close()
                ws = self._connect_websocket(self.LIQUIDATION_WS_URL)
                if not ws: break
            except Exception as e:
                logger.error(f"An unexpected error in liquidation WebSocket thread: {e}", exc_info=True)
                time.sleep(5)

    def _mark_price_ws_thread_func(self):
        """Thread untuk menangani stream mark price."""
        ws = self._connect_websocket(self.MARK_PRICE_WS_URL)
        if not ws: return

        while not self.shutdown_event.is_set():
            try:
                ready_to_read, _, _ = select.select([ws.sock], [], [], 1.0)
                if not ready_to_read:
                    try:
                        ws.ping()
                    except Exception as ping_err:
                         logger.warning(f"Failed to send ping on mark price stream: {ping_err}. Reconnecting...")
                         raise WebSocketConnectionClosedException("Ping failed")
                    continue

                messages = json.loads(ws.recv())
                # Pesan dari !markPrice@arr adalah sebuah list
                with self.data_lock:
                    for data in messages:
                        symbol = data.get('s')
                        if symbol and symbol in self.valid_symbols:
                            new_price = float(data['p'])
                            # Simpan update untuk dikirim secara batch
                            self.pending_price_updates[symbol] = new_price
                            self.mark_prices[symbol] = new_price
                            # Update harga BTC index jika simbol adalah BTCUSDT
                            if symbol == 'BTCUSDT':
                                self.btc_price_index = new_price
                                self.btc_index_last_updated = datetime.utcnow()


            except (WebSocketConnectionClosedException, json.JSONDecodeError, AttributeError, socket.timeout, OSError) as e:
                logger.error(f"WebSocket error in mark price stream: {e}. Reconnecting...")
                ws.close()
                ws = self._connect_websocket(self.MARK_PRICE_WS_URL)
                if not ws: break
            except Exception as e:
                 logger.error(f"An unexpected error in mark price WebSocket thread: {e}", exc_info=True)
                 time.sleep(5)

    # --- Data Processing ---
    def _process_depth_updates_from_queue(self):
        """Thread untuk memproses update order book dari queue secara terpisah."""
        while not self.shutdown_event.is_set():
            try:
                # Proses semua item yang ada di queue tanpa blocking
                while not self.depth_queue.empty():
                    data = self.depth_queue.get_nowait()
                    symbol = data.get('s', '').upper()
                    if not symbol or symbol not in self.valid_symbols:
                        continue

                    # Update order book
                    with self.data_lock:
                        # Bids (penawaran beli)
                        for p, q in data.get('b', []):
                            price, qty = float(p), float(q)
                            if qty == 0:
                                self.order_books[symbol]['bids'].pop(price, None)
                            else:
                                self.order_books[symbol]['bids'][price] = qty
                        # Asks (penawaran jual)
                        for p, q in data.get('a', []):
                            price, qty = float(p), float(q)
                            if qty == 0:
                                self.order_books[symbol]['asks'].pop(price, None)
                            else:
                                self.order_books[symbol]['asks'][price] = qty
                # Beri jeda singkat agar tidak membebani CPU
                time.sleep(0.01)
            except queue.Empty:
                time.sleep(0.05) # Tunggu jika queue kosong
            except Exception as e:
                logger.error(f"Error processing depth queue: {e}", exc_info=True)

    def _process_trade_data(self, data: Dict):
        """Memproses data perdagangan agregat."""
        symbol = data['s']
        price = float(data['p'])
        qty = float(data['q'])
        is_buyer_maker = data['m']
        trade_value = price * qty

        with self.data_lock:
            self.last_prices[symbol] = price
            # Tambahkan ke akumulator volume
            if is_buyer_maker: # Buyer is maker -> Sell trade
                self.volume_accumulator[symbol]['sell'] += trade_value
            else: # Seller is maker -> Buy trade
                self.volume_accumulator[symbol]['buy'] += trade_value
            # Tambahkan ke history harga
            self.price_history[symbol].append((datetime.utcnow(), price))


    def _process_liquidation_data(self, data: Dict):
        """Memproses data likuidasi."""
        symbol = data['s']
        if symbol not in self.valid_symbols:
            return

        side = data['S']
        price = float(data['p'])
        qty = float(data['q'])
        liq_value = price * qty

        with self.data_lock:
            now = datetime.utcnow()
            # Tambahkan ke akumulator likuidasi
            if side == 'BUY': # Liquidation of a SHORT position
                self.liquidation_accumulator[symbol]['buy'] += liq_value
                self.liquidation_history[symbol].append((now, liq_value, 0))
            elif side == 'SELL': # Liquidation of a LONG position
                self.liquidation_accumulator[symbol]['sell'] += liq_value
                self.liquidation_history[symbol].append((now, 0, liq_value))

    def _process_kline_data(self, data: Dict):
        """Memproses data kline dari WebSocket."""
        kline_data = data['k']
        symbol = data['s']
        start_time_dt = datetime.utcfromtimestamp(kline_data['t'] / 1000)
        is_closed = kline_data['x']

        new_candle_data = {
            'open': float(kline_data['o']),
            'high': float(kline_data['h']),
            'low': float(kline_data['l']),
            'close': float(kline_data['c']),
            'volume': float(kline_data['v']),
            'start_time': start_time_dt
        }

        with self.data_lock:
            # Jika ini adalah candle baru (waktu mulai berbeda dari yang terakhir)
            last_timestamp = self.last_candle_timestamps.get(symbol)
            if last_timestamp is None or start_time_dt > last_timestamp:
                # Candle sebelumnya sekarang menjadi candle yang baru saja ditutup
                self.previous_candle[symbol] = self.current_candle.get(symbol)
                # Simpan candle baru sebagai candle saat ini
                self.current_candle[symbol] = new_candle_data
                self.last_candle_timestamps[symbol] = start_time_dt

                # PERBAIKAN: Hanya jalankan autobot saat candle baru terbentuk
                # if self.previous_candle.get(symbol): # Pastikan ada candle sebelumnya
                #    self._run_autobot_logic(symbol)

            # Jika tidak, cukup update candle saat ini
            else:
                self.current_candle[symbol] = new_candle_data


    def _run_autobot_logic(self, symbol):
        """Menjalankan logika autobot untuk satu simbol saat candle baru terbentuk."""
        try:
            # Dapatkan data yang diperlukan di dalam lock
            with self.data_lock:
                mark_price = self.mark_prices.get(symbol)
                current_candle_time = self.last_candle_timestamps.get(symbol)

            # Dapatkan sinyal dari database di luar lock
            signal_data = self._get_signal_data_from_db(symbol)

            if not all([mark_price, current_candle_time, signal_data]):
                # logger.warning(f"Autobot [{symbol}]: Melewati, data tidak lengkap.")
                return

            recommendation = signal_data.get('Rekomendasi')
            signal_priority = signal_data.get('SignalPriority', 0)

            # Logika open posisi hanya untuk sinyal prioritas tinggi
            if signal_priority >= 1:
                if recommendation == 'Strong LONG':
                    logger.info(f"Autobot: Sinyal Strong LONG terdeteksi untuk {symbol}")
                    self._autobot_open_position(symbol, 'LONG', mark_price, current_candle_time)
                elif recommendation == 'Strong SHORT':
                    logger.info(f"Autobot: Sinyal Strong SHORT terdeteksi untuk {symbol}")
                    self._autobot_open_position(symbol, 'SHORT', mark_price, current_candle_time)
        except Exception as e:
            logger.error(f"Error pada logika autobot untuk {symbol}: {e}", exc_info=True)


    def _periodic_data_processor(self):
        """
        Thread yang berjalan secara periodik untuk memproses data yang terakumulasi,
        menghitung metrik, dan mendeteksi sinyal.
        """
        while not self.shutdown_event.wait(self.SIGNAL_DETECTION_INTERVAL):
            try:
                current_time = datetime.utcnow()
                # Buat salinan data yang perlu diproses untuk menghindari locking terlalu lama
                with self.data_lock:
                    symbols_to_process = list(self.valid_symbols)
                    # Salin data yang akan direset
                    liq_acc = self.liquidation_accumulator.copy()
                    vol_acc = self.volume_accumulator.copy()
                    # Reset akumulator
                    for symbol in self.valid_symbols:
                        self.liquidation_accumulator[symbol] = {'buy': 0, 'sell': 0}
                        self.volume_accumulator[symbol] = {'buy': 0, 'sell': 0}

                # Proses setiap simbol
                for symbol in symbols_to_process:
                    self._process_symbol_data(symbol, current_time, liq_acc, vol_acc)
                
                # Setelah memproses semua simbol, jalankan logika autobot
                # Logika ini dipindahkan ke saat candle baru terbentuk (_process_kline_data)
                # agar tidak berjalan setiap 2 detik.
                # Namun, kita bisa tetap menjalankannya di sini sebagai fallback
                # atau untuk logika yang tidak bergantung pada candle.
                for symbol in symbols_to_process:
                    self._run_autobot_logic(symbol)


            except Exception as e:
                logger.error(f"Error in periodic data processor: {e}", exc_info=True)


    def _process_symbol_data(self, symbol: str, current_time: datetime, liq_acc: dict, vol_acc: dict):
        """Memproses data untuk satu simbol."""
        try:
            # Dapatkan data dari akumulator yang disalin
            buy_liq = liq_acc.get(symbol, {}).get('buy', 0)
            sell_liq = liq_acc.get(symbol, {}).get('sell', 0)
            buy_vol = vol_acc.get(symbol, {}).get('buy', 0)
            sell_vol = vol_acc.get(symbol, {}).get('sell', 0)

            with self.data_lock:
                # Ambil data yang diperlukan dari struktur data utama
                mark_price = self.mark_prices.get(symbol)
                last_price = self.last_prices.get(symbol, mark_price)
                order_book = self.order_books.get(symbol)
                liq_history = self.liquidation_history.get(symbol)

                if not all([mark_price, last_price, order_book, liq_history is not None]):
                    return # Skip jika data tidak lengkap

                # --- Perhitungan Metrik ---
                # 1. Order Book Imbalance (OBI)
                bids_value = sum(p * q for p, q in order_book['bids'].items())
                asks_value = sum(p * q for p, q in order_book['asks'].items())
                total_book_value = bids_value + asks_value
                obi = ((bids_value - asks_value) / total_book_value) * 100 if total_book_value > 0 else 0

                # 2. Cumulative Volume Delta (CVD)
                cvd = buy_vol - sell_vol

                # 3. Liquidation Delta
                liq_delta = buy_liq - sell_liq

                # 4. Rata-rata Likuidasi dalam Jendela Waktu
                window_start_time = current_time - timedelta(minutes=self.LIQ_HISTORY_WINDOW)
                recent_buy_liq = sum(bl for ts, bl, _ in liq_history if ts > window_start_time)
                recent_sell_liq = sum(sl for ts, _, sl in liq_history if ts > window_start_time)
                avg_buy_liq_per_min = (recent_buy_liq / self.LIQ_HISTORY_WINDOW) if recent_buy_liq > 0 else 0
                avg_sell_liq_per_min = (recent_sell_liq / self.LIQ_HISTORY_WINDOW) if recent_sell_liq > 0 else 0


                # Simpan hasil perhitungan ke display_data
                self.display_data[symbol].update({
                    'last_price': last_price,
                    'mark_price': mark_price,
                    'cvd': cvd,
                    'buy_liq': buy_liq,
                    'sell_liq': sell_liq,
                    'liq_delta': liq_delta,
                    'obi': obi,
                    'avg_buy_liq_min': avg_buy_liq_per_min,
                    'avg_sell_liq_min': avg_sell_liq_per_min,
                })

        except Exception as e:
            logger.error(f"Error processing data for symbol {symbol}: {e}", exc_info=True)



    # --- Sinyal dan Database ---
    def _reload_data_from_db_periodically(self):
        """Memuat ulang data dari database secara periodik."""
        while not self.shutdown_event.wait(60): # Muat ulang setiap 60 detik
             try:
                # logger.info("Periodically reloading signal data from database...")
                cnxn = self._get_db_connection()
                cursor = cnxn.cursor()
                # Query untuk mengambil semua data yang relevan dalam satu panggilan
                query = """
                SELECT Symbol, Rekomendasi, SignalPriority,
                       TP1_LONG, SL_LONG, TP1_SHORT, SL_SHORT,
                       Rekomendasi_PSAR, Rekomendasi_RSI, Rekomendasi_MACD, Rekomendasi_Stochastic
                FROM F_ANALISA_TEKNIKAL_15M;
                """
                cursor.execute(query)
                rows = cursor.fetchall()

                temp_cache = {}
                for row in rows:
                    symbol = row.Symbol
                    temp_cache[symbol] = {
                        "Rekomendasi": row.Rekomendasi,
                        "SignalPriority": row.SignalPriority,
                        "TP1_LONG": row.TP1_LONG,
                        "SL_LONG": row.SL_LONG,
                        "TP1_SHORT": row.TP1_SHORT,
                        "SL_SHORT": row.SL_SHORT,
                        "Rekomendasi_PSAR": row.Rekomendasi_PSAR,
                        "Rekomendasi_RSI": row.Rekomendasi_RSI,
                        "Rekomendasi_MACD": row.Rekomendasi_MACD,
                        "Rekomendasi_Stochastic": row.Rekomendasi_Stochastic
                    }

                # Update cache utama dengan aman
                with self.signal_cache_lock:
                    self.signal_data_cache = temp_cache
                # logger.info(f"Successfully reloaded and cached data for {len(temp_cache)} symbols from DB.")

                cursor.close()
                cnxn.close()
             except pyodbc.Error as db_err:
                logger.error(f"Database error during periodic reload: {db_err}")
             except Exception as e:
                logger.error(f"Unexpected error during periodic DB reload: {e}", exc_info=True)

    def _get_signal_data_from_db(self, symbol: str) -> Optional[Dict]:
        """Mengambil data sinyal dari cache."""
        with self.signal_cache_lock:
            return self.signal_data_cache.get(symbol)

    # --- Flask & Socket.IO ---
    def _prepare_data_for_client(self) -> List[Dict]:
        """Menyiapkan dan memformat data untuk dikirim ke klien."""
        formatted_data = []
        with self.data_lock:
            # Buat salinan untuk menghindari masalah konkurensi
            display_data_copy = self.display_data.copy()

        for symbol, data in display_data_copy.items():
            # Ambil data sinyal dari cache
            signal_data = self._get_signal_data_from_db(symbol)

            if signal_data:
                data.update(signal_data) # Gabungkan data dari sinyal

            # Pastikan semua kunci ada untuk menghindari KeyError
            data.setdefault('last_price', 0)
            data.setdefault('mark_price', 0)
            data.setdefault('open_interest', 0)
            data.setdefault('funding_rate', 0)
            data.setdefault('cvd', 0)
            data.setdefault('buy_liq', 0)
            data.setdefault('sell_liq', 0)
            data.setdefault('liq_delta', 0)
            data.setdefault('obi', 0)
            data.setdefault('avg_buy_liq_min', 0)
            data.setdefault('avg_sell_liq_min', 0)
            data.setdefault('Rekomendasi', 'N/A')
            data.setdefault('SignalPriority', 0)
            # Dan seterusnya untuk semua kunci dari database

            formatted_data.append(data)
        return formatted_data

    def _data_emitter_thread(self):
        """Thread untuk mengirim data ke klien secara periodik."""
        while not self.shutdown_event.wait(2): # Kirim setiap 2 detik
            try:
                # Cek apakah ada klien yang terhubung
                if not self.socketio.server.eio.sockets:
                    continue

                full_data = self._prepare_data_for_client()

                # Kirim data lengkap
                self.socketio.emit('full_data', full_data, namespace='/')

                # Kirim update harga yang tertunda secara terpisah
                with self.data_lock:
                    if self.pending_price_updates:
                        self.socketio.emit('price_updates', self.pending_price_updates, namespace='/')
                        self.pending_price_updates.clear()

            except Exception as e:
                logger.error(f"Error in data emitter thread: {e}", exc_info=True)

    # --- Flask Routes ---
    @login_required
    def dashboard(self):
        return render_template('dashboard.html')

    @login_required
    def index_redirect(self):
        return redirect(url_for('dashboard'))

    @login_required
    def manual_reload(self):
        logger.info("Manual data reload triggered by user.")
        # Jalankan reload di thread terpisah agar tidak memblokir request
        threading.Thread(target=self._reload_data_from_db_periodically, daemon=True).start()
        return jsonify(status="Reloading data from database in the background.")

    def health_check(self):
        return jsonify(status="ok", timestamp=datetime.utcnow().isoformat())

    @login_required
    def symbol_info(self):
        """Endpoint untuk menyediakan info simbol (minQty, etc.) ke frontend."""
        if not self.symbol_info_map:
            self._fetch_symbol_info_map() # Coba fetch jika kosong
        return jsonify(self.symbol_info_map)


    @login_required
    def account_balance(self):
        """Endpoint untuk mendapatkan saldo akun."""
        current_time = time.time()
        # Cek cache terlebih dahulu
        if self.account_balance_cache and (current_time - self.balance_cache_time) < self.balance_refresh_interval:
            return jsonify({'success': True, 'balance': self.account_balance_cache})

        try:
            balance_data = self._fetch_binance_balance()
            if balance_data:
                # Cari balance USDT
                usdt_balance = next((item for item in balance_data if item['asset'] == 'USDT'), None)
                if usdt_balance:
                    available_balance = float(usdt_balance['availableBalance'])
                    # Update cache
                    self.account_balance_cache = {'USDT': available_balance}
                    self.balance_cache_time = current_time
                    return jsonify({'success': True, 'balance': self.account_balance_cache})

            return jsonify({'success': False, 'msg': 'USDT balance not found'})

        except Exception as e:
            logger.error(f"Error fetching account balance: {e}")
            return jsonify({'success': False, 'msg': str(e)}), 500


    def _generate_signature(self, params: Dict) -> str:
        """Menghasilkan signature HMAC-SHA256 untuk request Binance."""
        query_string = urllib.parse.urlencode(params)
        return hmac.new(self.BINANCE_API_SECRET.encode('utf-8'), msg=query_string.encode('utf-8'), digestmod=hashlib.sha256).hexdigest()

    def _fetch_binance_balance(self):
        """Mengambil data balance dari Binance API."""
        url = self.ACCOUNT_BALANCE_URL
        params = {
            'timestamp': int(time.time() * 1000)
        }
        params['signature'] = self._generate_signature(params)
        headers = {'X-MBX-APIKEY': self.BINANCE_API_KEY}
        try:
            response = self.session.get(url, params=params, headers=headers, timeout=10)
            response.raise_for_status()
            return response.json()
        except requests.RequestException as e:
            logger.error(f"Error fetching Binance balance: {e.response.text if e.response else e}")
            return None

    def _place_binance_order(self, symbol: str, side: OrderSide, order_type: OrderType, quantity: str, price: Optional[str] = None, reduce_only: Optional[bool] = False) -> Dict:
        """Menempatkan order ke Binance."""
        url = "https://fapi.binance.com/fapi/v1/order"
        params = {
            'symbol': symbol,
            'side': side.value,
            'type': order_type.value,
            'quantity': quantity,
            'timestamp': int(time.time() * 1000)
        }
        if order_type == OrderType.LIMIT:
            params['timeInForce'] = 'GTC'  # Good Till Cancelled
            params['price'] = price

        if reduce_only:
            params['reduceOnly'] = 'true'

        params['signature'] = self._generate_signature(params)
        headers = {'X-MBX-APIKEY': self.BINANCE_API_KEY}

        try:
            response = self.session.post(url, params=params, headers=headers, timeout=10)
            response_data = response.json()
            if response.status_code == 200 or response.status_code == 201:
                return {'success': True, 'data': response_data}
            else:
                return {'success': False, 'msg': response_data.get('msg', 'Unknown error'), 'code': response_data.get('code', 0)}
        except requests.RequestException as e:
            logger.error(f"Error placing Binance order: {e}")
            return {'success': False, 'msg': str(e)}


    @login_required
    def submit_order(self):
        """Menerima dan memproses order dari frontend."""
        try:
            # 1. Ambil data dari request
            data = request.get_json()
            if not data:
                return jsonify({'success': False, 'msg': 'Invalid request data'}), 400

            symbol = data.get('symbol')
            side = data.get('side')  # 'LONG' or 'SHORT'
            order_type_str = data.get('order_type', 'market').upper() # 'market' or 'limit'
            order_cost_str = data.get('order_cost')  # Dalam USDT
            leverage_str = data.get('leverage')
            open_price_str = data.get('open_price') # Hanya untuk LIMIT order
            stop_loss_str = data.get('stop_loss')
            take_profit_str = data.get('take_profit')

            # Validasi input dasar
            if not all([symbol, side, order_type_str, order_cost_str, leverage_str]):
                return jsonify({'success': False, 'msg': 'Missing required fields'}), 400
            if side not in ['LONG', 'SHORT']:
                return jsonify({'success': False, 'msg': 'Invalid side'}), 400

            # 2. Konversi dan Validasi Input Numerik
            try:
                order_cost = float(order_cost_str)
                leverage = int(leverage_str)
                order_type = OrderType(order_type_str)
                open_price = float(open_price_str) if open_price_str else None
                stop_loss = float(stop_loss_str) if stop_loss_str else None
                take_profit = float(take_profit_str) if take_profit_str else None

                if order_cost <= 0 or leverage <= 0:
                     return jsonify({'success': False, 'msg': 'Order cost and leverage must be positive'}), 400
                if order_type == OrderType.LIMIT and not open_price:
                     return jsonify({'success': False, 'msg': 'Limit price is required for LIMIT orders'}), 400

            except (ValueError, TypeError) as e:
                return jsonify({'success': False, 'msg': f"Invalid number format: {e}"}), 400

            # 3. Dapatkan Info Simbol & Harga Mark
            symbol_info = self.symbol_info_map.get(symbol)
            if not symbol_info:
                return jsonify({'success': False, 'msg': f'Symbol info for {symbol} not found.'}), 404

            with self.data_lock:
                mark_price = self.mark_prices.get(symbol)

            if not mark_price:
                 return jsonify({'success': False, 'msg': f'Mark price for {symbol} not available.'}), 404

            # Tentukan harga acuan untuk perhitungan kuantitas
            price_reference = open_price if order_type == OrderType.LIMIT and open_price else mark_price
            if not price_reference or price_reference <= 0:
                return jsonify({'success': False, 'msg': 'Invalid price reference for quantity calculation'}), 400


            # 4. === PERHITUNGAN KUANTITAS (UPGRADED) ===
            # Sesuai permintaan, Kuantitas = Order Cost * Leverage
            # PERHATIAN: Perhitungan ini tidak biasa. Secara umum, kuantitas dihitung sebagai (Order Cost * Leverage) / Harga Aset.
            quantity = order_cost * leverage


            # 5. Validasi dan Format Kuantitas & Harga
            min_qty = symbol_info.get('minQty', 0.0)
            step_size = str(symbol_info.get('stepSize', '0.0'))
            min_notional = symbol_info.get('minNotional', 0.0)
            tick_size = str(symbol_info.get('tickSize', '0.0'))

            # Validasi Notional Value
            if (quantity * price_reference) < min_notional:
                return jsonify({'success': False, 'msg': f"Notional value is too small. Minimum is ${min_notional}"}), 400

            # Validasi Minimum Quantity
            if quantity < min_qty:
                return jsonify({'success': False, 'msg': f"Quantity is too small. Minimum is {min_qty}"}), 400

            # Format kuantitas dan harga sesuai aturan Binance
            formatted_quantity = self._format_value(quantity, step_size)
            formatted_price = self._format_value(open_price, tick_size) if open_price else None

            logger.info(f"Order Prep: Symbol={symbol}, Side={side}, Qty={quantity}, Formatted Qty={formatted_quantity}, Price={open_price}, Formatted Price={formatted_price}")


            # 6. Atur Leverage di Binance
            try:
                self._set_leverage(symbol, leverage)
            except Exception as e:
                logger.error(f"Failed to set leverage for {symbol}: {e}")
                return jsonify({'success': False, 'msg': f"Failed to set leverage: {e}"}), 500

            # 7. Tempatkan Order ke Binance
            order_side_binance = OrderSide.BUY if side == 'LONG' else OrderSide.SELL
            binance_result = self._place_binance_order(
                symbol=symbol,
                side=order_side_binance,
                order_type=order_type,
                quantity=formatted_quantity,
                price=formatted_price
            )

            if not binance_result.get('success'):
                return jsonify({'success': False, 'msg': f"Binance error: {binance_result.get('msg')}", 'code': binance_result.get('code')}), 500

            binance_order_id = binance_result['data'].get('orderId')
            logger.info(f"Successfully placed order on Binance. Order ID: {binance_order_id}")

            # 8. Simpan Order ke Database
            db_success = self._submit_order_to_database(
                symbol=symbol,
                side=side,
                order_type=order_type.value,
                quantity=float(formatted_quantity),
                price=float(formatted_price if formatted_price else mark_price), # Simpan mark price untuk market order
                leverage=leverage,
                stop_loss=stop_loss,
                take_profit=take_profit,
                binance_order_id=str(binance_order_id),
                initial=True
            )

            if not db_success:
                 # Ini adalah kondisi kritis, order ada di Binance tapi tidak di DB lokal
                 logger.error(f"CRITICAL: Order {binance_order_id} placed on Binance but failed to save to local DB.")
                 return jsonify({'success': False, 'msg': 'Order placed but failed to save locally. Please check manually.'}), 500


            return jsonify({'success': True, 'msg': 'Order submitted successfully!', 'binance_order_id': binance_order_id})

        except Exception as e:
            logger.error(f"Error in submit_order: {e}", exc_info=True)
            return jsonify({'success': False, 'msg': f'An internal error occurred: {e}'}), 500


    def _submit_order_to_database(self, symbol: str, side: str, order_type: str, quantity: float, price: float, leverage: int, stop_loss: Optional[float], take_profit: Optional[float], binance_order_id: str, initial: bool) -> bool:
        """Menyimpan atau memperbarui order di database."""
        try:
            cnxn = self._get_db_connection()
            cursor = cnxn.cursor()

            # Jika 'initial' adalah True, ini adalah order baru (INSERT)
            if initial:
                # Dapatkan server time untuk OrderDate
                cursor.execute("SELECT GETDATE()")
                server_time = cursor.fetchone()[0]
                order_id = str(uuid.uuid4()) # Buat ID unik baru

                query = """
                INSERT INTO F_TRADING_POSITIONS
                (OrderID, Symbol, Position, Leverage, OrderCost, Quantity, OpenPrice, OrderDate, Status, BinanceOrderID, OrderType, StopLoss, TakeProfit)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """
                # OrderCost dihitung kembali untuk disimpan (meskipun tidak digunakan di logic utama)
                order_cost = (quantity * price) / leverage

                params = (
                    order_id, symbol, side, leverage, order_cost, quantity, price,
                    server_time, 1, binance_order_id, order_type, stop_loss, take_profit
                )
                logger.info(f"Executing INSERT to DB for Binance Order ID {binance_order_id}")
            else:
                 # Jika tidak, ini adalah pembaruan untuk order yang ada (UPDATE harga)
                query = "UPDATE F_TRADING_POSITIONS SET OpenPrice = ? WHERE BinanceOrderID = ?;"
                params = (price, binance_order_id)
                logger.info(f"Executing UPDATE to DB for Binance Order ID {binance_order_id}")


            cursor.execute(query, params)
            cnxn.commit()
            return True
        except pyodbc.Error as db_err:
            logger.error(f"Database error submitting order {binance_order_id}: {db_err}")
            return False
        except Exception as e:
            logger.error(f"Unexpected error submitting order {binance_order_id} to DB: {e}")
            return False
        finally:
            if 'cursor' in locals() and cursor:
                cursor.close()
            if 'cnxn' in locals() and cnxn:
                cnxn.close()


    # --- Open Orders Page Logic ---
    @login_required
    def open_orders_page(self):
        """Menyajikan halaman open orders."""
        return render_template('open_orders.html')

    @login_required
    def get_open_orders(self):
        """API endpoint untuk mengambil data open orders dari cache."""
        with self.open_orders_lock:
            if self.open_orders_cache is None:
                # Jika cache kosong, coba ambil langsung dari DB
                try:
                    orders = self._fetch_open_orders_data()
                    self.open_orders_cache = orders
                    self.open_orders_last_updated = time.time()
                    return jsonify(orders)
                except Exception as e:
                    logger.error(f"Error fetching open orders directly: {e}")
                    return jsonify({"error": "Failed to fetch open orders"}), 500
            return jsonify(self.open_orders_cache)


    def _fetch_open_orders_data(self):
        """Mengambil data order yang aktif dari database."""
        try:
            cnxn = self._get_db_connection()
            cursor = cnxn.cursor()
            # Query untuk mengambil order yang berstatus 1 (Aktif)
            query = """
            SELECT OrderID, Symbol, Position, Leverage, OrderCost, Quantity, OpenPrice, OrderDate, BinanceOrderID
            FROM F_TRADING_POSITIONS
            WHERE Status = 1
            ORDER BY OrderDate DESC;
            """
            cursor.execute(query)
            rows = cursor.fetchall()
            orders = []
            columns = [column[0] for column in cursor.description]
            for row in rows:
                orders.append(dict(zip(columns, row)))
            return orders
        finally:
            if 'cursor' in locals() and cursor: cursor.close()
            if 'cnxn' in locals() and cnxn: cnxn.close()


    @login_required
    def cancel_order(self):
        """Membatalkan order di Binance dan memperbarui database."""
        data = request.get_json()
        symbol = data.get('symbol')
        binance_order_id = data.get('binance_order_id')

        if not symbol or not binance_order_id:
            return jsonify({'success': False, 'msg': 'Symbol and Binance Order ID are required'}), 400

        logger.info(f"Attempting to cancel order {binance_order_id} for {symbol}")

        # 1. Batalkan order di Binance
        url = "https://fapi.binance.com/fapi/v1/order"
        params = {
            'symbol': symbol,
            'orderId': binance_order_id,
            'timestamp': int(time.time() * 1000)
        }
        params['signature'] = self._generate_signature(params)
        headers = {'X-MBX-APIKEY': self.BINANCE_API_KEY}

        try:
            response = self.session.delete(url, params=params, headers=headers, timeout=10)
            response_data = response.json()

            if response.status_code == 200:
                logger.info(f"Successfully cancelled order {binance_order_id} on Binance.")
                # 2. Update status di database menjadi 2 (Cancelled)
                update_success = self._update_order_status_by_binance_id(
                    binance_order_id, status=2, close_price=None
                )
                if update_success:
                    return jsonify({'success': True, 'msg': 'Order cancelled successfully.'})
                else:
                    logger.error(f"CRITICAL: Order {binance_order_id} cancelled on Binance but failed to update status in DB.")
                    return jsonify({'success': False, 'msg': 'Order cancelled on Binance, but failed to update local status.'}), 500
            else:
                 # Cek apakah order sudah tidak ada (misal sudah terisi atau dibatalkan manual)
                if response_data.get('code') == -2011: # "Unknown order sent."
                    logger.warning(f"Order {binance_order_id} not found on Binance. It might be already filled or cancelled.")
                    # Mungkin kita ingin menganggap ini sebagai "sukses" dari sisi klien
                    # dan membiarkan proses lain (seperti pengecekan posisi) mengurus statusnya.
                    return jsonify({'success': True, 'msg': 'Order not found on Binance, it may have been filled or already cancelled.'})
                else:
                    logger.error(f"Failed to cancel order {binance_order_id} on Binance: {response_data.get('msg')}")
                    return jsonify({'success': False, 'msg': f"Binance error: {response_data.get('msg')}"}), 500

        except requests.RequestException as e:
            logger.error(f"Request error while cancelling order {binance_order_id}: {e}")
            return jsonify({'success': False, 'msg': f"Request error: {e}"}), 500


    def _fetch_binance_order_detail(self, order_id: int, symbol: str) -> Optional[Dict]:
        """Mengambil detail order dari Binance."""
        url = "https://fapi.binance.com/fapi/v1/order"
        params = {
            'symbol': symbol,
            'orderId': order_id,
            'timestamp': int(time.time() * 1000)
        }
        params['signature'] = self._generate_signature(params)
        headers = {'X-MBX-APIKEY': self.BINANCE_API_KEY}
        try:
            response = self.session.get(url, params=params, headers=headers, timeout=10)
            response.raise_for_status()
            return response.json()
        except requests.RequestException as e:
            logger.error(f"Error fetching order detail for {order_id}: {e.response.text if e.response else e}")
            return None


    def _update_order_price_by_binance_id(self, binance_order_id: str, price: float) -> bool:
        """Memperbarui harga pembukaan order di database berdasarkan Binance Order ID."""
        try:
            cnxn = self._get_db_connection()
            cursor = cnxn.cursor()
            query = "UPDATE F_TRADING_POSITIONS SET OpenPrice = ? WHERE BinanceOrderID = ? AND Status = 1;"
            cursor.execute(query, price, binance_order_id)
            cnxn.commit()
            # Cek apakah ada baris yang terpengaruh
            if cursor.rowcount > 0:
                logger.info(f"Price for order {binance_order_id} updated to {price} in DB.")
                return True
            else:
                logger.warning(f"No order found with Binance ID {binance_order_id} to update price.")
                return False
        except pyodbc.Error as e:
            logger.error(f"Database error updating price for order {binance_order_id}: {e}")
            return False
        finally:
            if 'cursor' in locals(): cursor.close()
            if 'cnxn' in locals(): cnxn.close()


    @login_required
    def close_order(self):
        """Menutup posisi di Binance dan memperbarui database."""
        data = request.get_json()
        order_id = data.get('order_id') # Ini adalah OrderID dari database kita
        symbol = data.get('symbol')
        position = data.get('position') # LONG or SHORT
        quantity = data.get('quantity')

        if not all([order_id, symbol, position, quantity]):
             return jsonify({'success': False, 'msg': 'Missing required data for closing order'}), 400

        # Tentukan sisi order untuk menutup posisi
        close_side = OrderSide.SELL if position == 'LONG' else OrderSide.BUY

        logger.info(f"Attempting to close {position} position for {symbol} with quantity {quantity}")

        # Tempatkan MARKET order untuk menutup posisi
        close_result = self._place_binance_order(
            symbol=symbol,
            side=close_side,
            order_type=OrderType.MARKET,
            quantity=str(quantity),
            reduce_only=True # Parameter PENTING untuk memastikan hanya menutup posisi
        )

        if close_result.get('success'):
            logger.info(f"Successfully submitted closing order for DB OrderID {order_id}")

            # Beri jeda singkat agar order terisi dan bisa di-query
            time.sleep(1)
            closed_order_id_binance = close_result['data'].get('orderId')
            close_price = 0.0

            try:
                # Ambil detail order yang baru saja dibuat untuk mendapatkan harga eksekusi
                closed_order_details = self._fetch_binance_order_detail(closed_order_id_binance, symbol)
                if closed_order_details and closed_order_details.get('status') == 'FILLED':
                    close_price = float(closed_order_details.get('avgPrice', 0))
                    logger.info(f"Close order {closed_order_id_binance} filled at average price: {close_price}")
                else:
                    logger.warning(f"Could not confirm fill price for closing order {closed_order_id_binance}. Using mark price as fallback.")
                    with self.data_lock:
                        close_price = self.mark_prices.get(symbol, 0)

            except Exception as e:
                 logger.error(f"Error fetching close order details: {e}")
                 with self.data_lock:
                    close_price = self.mark_prices.get(symbol, 0)


            # Update status di database menjadi 0 (Closed)
            update_success = self._update_order_status_by_db_id(
                order_id, status=0, close_price=close_price
            )

            if update_success:
                return jsonify({'success': True, 'msg': f'Position closed successfully at price ≈ {close_price:.4f}'})
            else:
                logger.error(f"CRITICAL: Position for OrderID {order_id} closed on Binance but failed to update status in DB.")
                return jsonify({'success': False, 'msg': 'Position closed on Binance, but failed to update local status.'}), 500

        else:
            logger.error(f"Failed to close position for OrderID {order_id}: {close_result.get('msg')}")
            return jsonify({'success': False, 'msg': f"Binance error: {close_result.get('msg')}"}), 500


    def _update_order_status_by_db_id(self, order_id: str, status: int, close_price: Optional[float]) -> bool:
        """Memperbarui status order di database berdasarkan OrderID (dari DB)."""
        try:
            cnxn = self._get_db_connection()
            cursor = cnxn.cursor()
            # Dapatkan waktu server untuk CloseDate
            cursor.execute("SELECT GETDATE()")
            server_time = cursor.fetchone()[0]

            query = """
            UPDATE F_TRADING_POSITIONS
            SET Status = ?, ClosePrice = ?, CloseDate = ?
            WHERE OrderID = ?;
            """
            cursor.execute(query, status, close_price, server_time, order_id)
            cnxn.commit()
            return cursor.rowcount > 0
        except pyodbc.Error as e:
            logger.error(f"Database error updating status for order {order_id}: {e}")
            return False
        finally:
            if 'cursor' in locals(): cursor.close()
            if 'cnxn' in locals(): cnxn.close()


    def _update_order_status_by_binance_id(self, binance_order_id: str, status: int, close_price: Optional[float]) -> bool:
        """Memperbarui status order di database berdasarkan BinanceOrderID."""
        try:
            cnxn = self._get_db_connection()
            cursor = cnxn.cursor()
            # Dapatkan waktu server untuk CloseDate jika order ditutup/dibatalkan
            close_date = None
            if status in [0, 2]: # 0=Closed, 2=Cancelled
                cursor.execute("SELECT GETDATE()")
                close_date = cursor.fetchone()[0]

            query = "UPDATE F_TRADING_POSITIONS SET Status = ?, ClosePrice = ?, CloseDate = ? WHERE BinanceOrderID = ?;"
            cursor.execute(query, status, close_price, close_date, binance_order_id)
            cnxn.commit()

            if cursor.rowcount > 0:
                logger.info(f"Status for Binance order {binance_order_id} updated to {status} in DB.")
                return True
            else:
                logger.warning(f"No order found with Binance ID {binance_order_id} to update status.")
                return False
        except pyodbc.Error as e:
            logger.error(f"Database error updating status for Binance order {binance_order_id}: {e}")
            return False
        finally:
            if 'cursor' in locals(): cursor.close()
            if 'cnxn' in locals(): cnxn.close()


    # --- Socket.IO Handlers ---
    def handle_connect(self):
        logger.info(f"Client connected: {request.sid}")

    def handle_disconnect(self):
        logger.info(f"Client disconnected: {request.sid}")

    def handle_error(self, e):
        logger.error(f"Socket.IO error: {e}")

    def handle_request_data(self):
        """Handle permintaan data awal dari klien."""
        logger.info(f"Received initial data request from client {request.sid}")
        initial_data = self._prepare_data_for_client()
        emit('full_data', initial_data)


    def _handle_shutdown(self, signum, frame):
        """Menangani sinyal shutdown dengan bersih."""
        logger.info(f"Shutdown signal received ({signum}). Cleaning up...")
        self.shutdown_event.set()
        # Beri waktu untuk thread-thread selesai
        time.sleep(2)
        # Hentikan server Socket.IO
        self.socketio.stop()
        logger.info("Shutdown complete.")
        # Keluar dari proses
        sys.exit(0)

    # --- Main Execution ---
    def run(self):
        """Memulai semua proses dan server Flask."""
        signal.signal(signal.SIGINT, self._handle_shutdown)
        signal.signal(signal.SIGTERM, self._handle_shutdown)

        self.load_symbols()
        self._fetch_exchange_info()
        self._fetch_symbol_info_map() # Panggil setelah valid_symbols diisi
        self._initialize_data()

        # Buat daftar stream WebSocket
        streams = self._get_websocket_streams()
        # Bagi menjadi beberapa koneksi jika jumlah stream terlalu banyak
        # Binance memperbolehkan hingga 200 stream per koneksi
        chunk_size = 150
        stream_chunks = [streams[i:i + chunk_size] for i in range(0, len(streams), chunk_size)]

        # --- Mulai semua thread latar belakang ---
        # 1. Thread untuk koneksi WebSocket utama (bisa lebih dari satu)
        for i, chunk in enumerate(stream_chunks):
             threading.Thread(target=self._websocket_thread_func, args=(chunk,), name=f"MainWS-{i+1}", daemon=True).start()

        # 2. Thread untuk stream likuidasi
        threading.Thread(target=self._liquidation_ws_thread_func, name="LiquidationWS", daemon=True).start()

        # 3. Thread untuk stream mark price
        threading.Thread(target=self._mark_price_ws_thread_func, name="MarkPriceWS", daemon=True).start()

        # 4. Thread untuk memproses update order book dari queue
        threading.Thread(target=self._process_depth_updates_from_queue, name="DepthProcessor", daemon=True).start()

        # 5. Thread untuk memproses data secara periodik
        threading.Thread(target=self._periodic_data_processor, name="DataProcessor", daemon=True).start()

        # 6. Thread untuk memuat ulang data dari DB
        threading.Thread(target=self._reload_data_from_db_periodically, name="DBReloader", daemon=True).start()

        # 7. Thread untuk mengirim data ke klien
        threading.Thread(target=self._data_emitter_thread, name="DataEmitter", daemon=True).start()

        # 8. Thread untuk memperbarui data open orders
        threading.Thread(target=self._open_orders_updater, name="OpenOrdersUpdater", daemon=True).start()

        # 9. Thread untuk memperbarui mark price di halaman open orders
        threading.Thread(target=self._periodic_mark_price_updater, name="MarkPriceUpdater", daemon=True).start()


        logger.info("Starting Flask-SocketIO server...")
        try:
            # Gunakan host '0.0.0.0' agar bisa diakses dari luar container/VM
            self.socketio.run(self.flask_app, host='0.0.0.0', port=5000, debug=False, use_reloader=False, allow_unsafe_werkzeug=True)
        except Exception as e:
            logger.error(f"Failed to start Flask-SocketIO server: {e}", exc_info=True)
            self.shutdown_event.set()


    def _open_orders_updater(self):
        """Thread untuk memperbarui data open orders setiap 10 detik"""
        while not self.shutdown_event.wait(15):
            try:
                # logger.info("Memperbarui data open orders...")

                # Ambil data dari database
                orders_data = self._fetch_open_orders_data()

                # Simpan di cache
                with self.open_orders_lock:
                    self.open_orders_cache = orders_data
                    self.open_orders_last_updated = time.time()

                # Kirim ke frontend
                self.socketio.emit('open_orders_update', orders_data, namespace='/')
            except Exception as e:
                logger.error(f"Error pembaruan open orders: {e}")

    def _periodic_mark_price_updater(self):
        """Thread untuk mengirim update mark price setiap 1 detik"""
        while not self.shutdown_event.wait(3):
            try:
                # Ambil snapshot mark prices
                with self.data_lock:
                    mark_prices = self.mark_prices.copy()

                # Kirim ke frontend
                self.socketio.emit('mark_price_update', mark_prices, namespace='/')
            except Exception as e:
                logger.error(f"Error pembaruan mark price: {e}")

if __name__ == "__main__":
    try:
        detector = SignalDetector()
        detector.run()
    except Exception as e:
        logger.critical(f"A critical error occurred in the main execution block: {e}", exc_info=True)
        sys.exit(1)
