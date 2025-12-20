import os
import sys
import time
import threading
import pygame
import winreg
import re
import bisect
from PIL import Image, ImageFilter
import numpy as np
import io
from io import BytesIO
import platform
import json
import ctypes
from urllib import parse
import random
import soco
import socket
from pathlib import Path
from http.server import HTTPServer, SimpleHTTPRequestHandler
from functools import partial  # 用于绑定参数
import threading
from PyQt5.QtWidgets import (QApplication, QLineEdit, QWidget, QCheckBox, 
                            QVBoxLayout, QHBoxLayout, QPushButton, QListWidget, 
                            QLabel, QFileDialog, QMessageBox, QProgressBar, 
                            QGraphicsDropShadowEffect, QSplitter, QAbstractItemView,QComboBox,QAbstractItemView)
from PyQt5.QtCore import Qt, pyqtSignal, QTimer, QPoint, QPropertyAnimation, QEasingCurve, QParallelAnimationGroup,QEvent
from PyQt5.QtGui import QColor,QPixmap, QIcon,QFont
import keyboard
from AcrylicEffect import WindowEffect  
from OnlineSongsGet import OnlineDownloader,TrackInfo
from mutagen.id3 import ID3, USLT ,APIC,TIT2
from mutagen.flac import FLAC,Picture
import winsdk.windows.media.playback as media_playback
import winsdk.windows.media
import winsdk.windows.storage.streams
from ctypes import wintypes
import winsdk.windows.foundation

# 初始化 SMTC



c=0#差值，pygame_music的get_pos有问题！
is_scrolling=False
no_scroll_event=0
downloading=False

class RECT(ctypes.Structure):
    _fields_ = [
        ('left', wintypes.LONG),
        ('top', wintypes.LONG),
        ('right', wintypes.LONG),
        ('bottom', wintypes.LONG),
    ]


class MusicPlayer(QWidget):
    # 自定义信号，用于更新UI
    update_ui_signal = pyqtSignal(int, int)  # 当前时间(ms)，总时间(ms)
    progress_update_signal = pyqtSignal(int, int)
    # 在非 GUI 线程请求在主线程播放（避免线程直接操作 GUI）
    play_request = pyqtSignal()
    def __init__(self):
        global lyric_files
        lyric_files=[]
        super().__init__()
        pygame.mixer.init()
        
        # 设置窗口透明相关属性
        self.setGeometry(0, 0, 700, 230)
        self.dlnamode=False
        self.search_result=[]
        self.search_result_index=0
        
        self.playlist = []
        self.current_index = 0
        self.is_playing = False
        self.music_long = 0  # 总时长(ms)
        self.quit_flag = 0
        self.maxvol=50 #开发用的，可调节
        self.show_flag = 1  # 初始化为显示状态
        self.playorder=0
        self.myip=socket.gethostbyname(socket.gethostname())
        self.port=random.randint(8000,10000)
        print(f"当前IP地址为：{self.myip}，端口为：{self.port}")
        # 记录 Sonos 上次的 transport state，避免切换设备时重复触发下一首
        self._last_soco_transport = None
        self.fix_std_streams()
        self.draging=False
        self.onlinemode=False
        self.remain_playlist=[]
        self.smtc_available=True
        self.online_download_map={}
        try:
            self._smtc_player = winsdk.windows.media.playback.MediaPlayer()
            self._smtc = self._smtc_player.system_media_transport_controls
            self._smtc.add_button_pressed(self._on_smtc_button_pressed)
            self._smtc.is_play_enabled = True
            self._smtc.is_pause_enabled = True
            self._smtc.is_next_enabled = True
            self._smtc.is_previous_enabled = True
            self._smtc_updater = self._smtc.display_updater
            self._smtc.playback_status = winsdk.windows.media.MediaPlaybackStatus.PLAYING
        except:
            self.smtc_available=False
        self.text_color = ""
        self.scroll_bg = ""
        self.scroll_handle = ""
        self.scroll_handle_hover = ""
        self.theme_color = ""
        self.theme_color2 = ""
        self.is_dark = False
        self.setWindowIcon(QIcon("vacuum_music_player.ico"))
        self.window_position="left"
        self.effect="Disabled"
        # 主题相关属性
        if platform.uname().system=="Windows":
            if int(platform.uname().version.split(".")[0])>=10:
                self.setAttribute(Qt.WA_TranslucentBackground)
                self.setWindowFlags(Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint)
                self.windowEffect = WindowEffect()
                self.effect="Acrylic"
                self.setAttribute(Qt.WA_NoSystemBackground)
                self.shadowcolor=QColor(0,0,0,180)
                
            elif int(platform.uname().version.split(".")[0])>=6:
                self.setAttribute(Qt.WA_TranslucentBackground)
                self.setWindowFlags(Qt.WindowMinimizeButtonHint)
                self.setFixedSize(self.size())
                self.setWindowFlags(Qt.WindowStaysOnTopHint)
                self.windowEffect=WindowEffect()
                self.effect="Aero"
                self.setAttribute(Qt.WA_NoSystemBackground)
                self.shadowcolor=QColor(255,255,255,180)
        self.init_ui()
        
        # 设置窗口效果
        
        # http server started flag，避免重复启动
        self._http_server_started = False
        # 更新UI主题
        self.update_ui_theme()
        # 关键修复：连接UI更新信号到处理函数
        self.update_ui_signal.connect(self.update_ui_handler)
        # 连接播放请求信号，确保 play_music 在主线程执行
        self.play_request.connect(self.play_music)
        self.searching_dlna_devices=QTimer(self)
        self.searching_dlna_devices.timeout.connect(lambda:self.search_dlna_devices(5))
        self.searching_dlna_devices.start(30000)  # 每30s搜索一次dlna设备
        if self.onlinemode==True:#强制开启，调试用
            self.online_downloader=OnlineDownloader()
            self.playlistid="" #change_there歌单id
            self.trackinfo=TrackInfo()
            self.onlinetrack=self.trackinfo.get_trackinfo(int(self.playlistid))
            self.playid=[]
            self.playname=[]
            for item in self.onlinetrack:
                self.playid.append(list(item)[0])
                self.playname.append(list(item)[1])
                self.playlist=self.playid.copy()
            self.current_index=0
            self.update_list_widget_online()
        else:
            self.load_music_playlist()
            if self.onlinemode==True:
                self.online_downloader=OnlineDownloader()
                self.trackinfo=TrackInfo()
                self.onlinetrack=self.trackinfo.get_trackinfo(int(self.playlistid))
                self.playid=[]
                self.playname=[]
                for item in self.onlinetrack:
                    self.playid.append(list(item)[0])
                    self.playname.append(list(item)[1])
                    self.playlist=self.playid.copy()
                self.current_index=0
                self.update_list_widget_online()
        self.start_music_thread()
        if self.dlnamode==True:
            self.start_http_server()
        
        # 创建定时器线程，用于刷新UI

        self.refresh_timer=QTimer(self)
        self.refresh_timer.timeout.connect(self.refresh_ui)
        self.refresh_timer.start(500)  # 每500ms刷新一次
        self.search_dlna_devices(0.5)
        
        self.hotkey_timer=QTimer(self)
        self.hotkey_timer.timeout.connect(self.hotkey)
        self.hotkey_timer.start(100)  # 每100ms检查一次热键
        
        # 初始化显示状态
        if self.show_flag:
            self.show()
        else:
            self.hide()
        self.raise_()
        self.activateWindow()
        self.start_progress_update()
        
        # 新增搜索窗口相关
        self.search_window = None
    def changeEvent(self, event):
        if event.type() == QEvent.WindowStateChange:
            if self.windowState() & Qt.WindowMinimized:
                self.showNormal()
                self.hide_show_window()
                return
            else:
                self.showNormal()

    class advanced_list_view(QListWidget):
        def __init__(self, parent=None):
            super().__init__(parent)
            self.setVerticalScrollMode(QListWidget.ScrollPerPixel)
            self.verticalScrollBar().setSingleStep(10)
        
        def wheelEvent(self, event):
            global is_scrolling
            global no_scroll_event
            # 通过父窗口访问 MusicPlayer 实例
            is_scrolling = True
            no_scroll_event = 0  # 重置计数器
                
            # 调用父类方法实现正常滚动
            super().wheelEvent(event)
            is_scrolling = False
        def setCurrentRow(self, row):
            # 保存当前滚动位置
            scroll_pos = self.verticalScrollBar().value()
            
            # 调用父类方法设置当前行
            super().setCurrentRow(row)
            
            # 恢复滚动位置
            self.verticalScrollBar().setValue(scroll_pos)
            
        def setCurrentItem(self, item):
            # 保存当前滚动位置
            scroll_pos = self.verticalScrollBar().value()
            
            # 调用父类方法设置当前项
            super().setCurrentItem(item)
            # 恢复滚动位置
            self.verticalScrollBar().setValue(scroll_pos)
    def _on_smtc_button_pressed(self,sender, args):
        """SMTC 按钮点击的回调函数"""
        # 获取点击的按钮类型（来自 media.MediaPlaybackControlButton 枚举）
        button_type = args.button
        
        if button_type == winsdk.windows.media.SystemMediaTransportControlsButton.PLAY:
            self._smtc.playback_status =  winsdk.windows.media.MediaPlaybackStatus.PLAYING
            self.toggle_play_pause()
    
        elif button_type == winsdk.windows.media.SystemMediaTransportControlsButton.PAUSE:
            self._smtc.playback_status =  winsdk.windows.media.MediaPlaybackStatus.PAUSED
            self.toggle_play_pause()
        
        elif button_type == winsdk.windows.media.SystemMediaTransportControlsButton.PREVIOUS:
            self.prev_song()
        
        elif button_type == winsdk.windows.media.SystemMediaTransportControlsButton.NEXT:
            self.next_song()
    def search_dlna_devices(self,timeout):
        # 发现设备，保证 devices 为稳定的列表（按 player_name 排序），避免不同次发现顺序变化导致索引漂移
        try:
            discovered = soco.discover(timeout=timeout)
        except Exception:
            discovered = None

        devices = []
        if discovered:
            try:
                devices = list(discovered)
                devices.sort(key=lambda d: getattr(d, 'player_name', '').lower())
            except Exception:
                devices = list(discovered)

        # 记录之前选中的设备（优先使用当前 soco_device 的 ip_address）
        prev_soco_ip = None
        try:
            if getattr(self, 'dlnamode', False) and getattr(self, 'soco_device', None):
                prev_soco_ip = getattr(self.soco_device, 'ip_address', None)
        except Exception:
            prev_soco_ip = None

        # 备份当前 combo 文本以便回退匹配
        try:
            prev_text = self.play_device_choose.currentText()
        except Exception:
            prev_text = None

        # 更新内部 devices 列表
        self.devices = devices

        # 重建下拉列表，期间屏蔽信号以避免触发 change_play_device
        try:
            self.play_device_choose.blockSignals(True)
        except Exception:
            pass
        self.play_device_choose.clear()
        self.play_device_choose.addItem("本机")
        for device in self.devices:
            try:
                self.play_device_choose.addItem(device.player_name)
            except Exception:
                # 忽略无法读取名称的设备
                self.play_device_choose.addItem("Unknown")

        # 尝试恢复之前的选择：优先按 IP 匹配，其次按名称匹配，最后回退到 本机
        restored_index = 0
        if prev_soco_ip:
            for i, d in enumerate(self.devices):
                if getattr(d, 'ip_address', None) == prev_soco_ip:
                    restored_index = i + 1
                    break
        if restored_index == 0 and prev_text and prev_text != "本机":
            for i, d in enumerate(self.devices):
                try:
                    if d.player_name == prev_text:
                        restored_index = i + 1
                        break
                except Exception:
                    continue

        try:
            self.play_device_choose.setCurrentIndex(restored_index)
        except Exception:
            pass

        try:
            self.play_device_choose.blockSignals(False)
        except Exception:
            pass
    def quit_musicplayer(self):
        self.quit_flag = 1
        pygame.mixer.music.stop()
        self.close()
    
    def init_ui(self):
        self.primary_screen = QApplication.primaryScreen().availableGeometry()
        self.setWindowTitle("音乐播放器")
        self.resize(700, 230)
        self.scroll_status=0
        # 主布局（水平布局，管理整个窗口）
        _main_layout = QHBoxLayout(self)  # 绑定到主窗口，无需再调用setLayout
        # 去掉顶层布局默认的内边距和间距，避免列表顶部出现不必要的空隙
        _main_layout.setContentsMargins(10, 10, 10, 10)
        _main_layout.setSpacing(0)

        # ---------------------- 左侧容器（包含列表、按钮、进度条） ----------------------
        self.left_widget = QWidget(self)  # 左侧容器，父对象为主窗口
        left_layout = QVBoxLayout(self.left_widget)  # 左侧容器的布局（垂直）
        # 左侧布局也清除内边距，让列表紧贴顶部
        left_layout.setContentsMargins(5, 0, 0, 0)

        # 1.1 歌曲列表
        self.list_widget = QListWidget(self.left_widget)  # 父对象设为left_widget，确保被其布局管理
        self.list_widget.itemClicked.connect(self.play_selected_song)
        left_layout.addWidget(self.list_widget)  # 加入左侧布局
        self.list_widget.setVerticalScrollMode(QListWidget.ScrollPerPixel)
        self.list_widget.verticalScrollBar().setSingleStep(10)

        # 1.2 按钮区域（水平布局）
        button_layout = QHBoxLayout()
        self.play_button = QPushButton("播放", self.left_widget)
        self.play_button.clicked.connect(self.toggle_play_pause)
        button_layout.addWidget(self.play_button)

        self.hide_show_button = QPushButton("隐藏/显示", self.left_widget)
        self.hide_show_button.clicked.connect(self.hide_show_window)
        button_layout.addWidget(self.hide_show_button)

        self.move_button = QPushButton("滚动到当前播放", self.left_widget)
        self.move_button.clicked.connect(self.to_now_playing)
        button_layout.addWidget(self.move_button)

        self.change_order_button = QPushButton("顺序播放", self.left_widget)
        self.change_order_button.clicked.connect(self.change_play_order)
        button_layout.addWidget(self.change_order_button)

        self.search_button = QPushButton("搜索", self.left_widget)
        self.search_button.clicked.connect(self.search)
        button_layout.addWidget(self.search_button)
        left_layout.addLayout(button_layout)  # 按钮布局加入左侧布局

        # 1.3 进度条区域（水平布局）
        progress_layout = QHBoxLayout()
        self.now_time_label = QLabel("00:00", self.left_widget)
        # 添加阴影（保持原有）
        shadow1 = QGraphicsDropShadowEffect()
        shadow1.setBlurRadius(10)
        shadow1.setXOffset(2)
        shadow1.setYOffset(2)
        shadow1.setColor(self.shadowcolor)
        self.play_device_choose=QComboBox(self.left_widget)
        self.play_device_choose.setFixedWidth(60)
        self.play_device_choose.view().adjustSize()
        self.play_device_choose.currentIndexChanged.connect(self.change_play_device)
        progress_layout.addWidget(self.play_device_choose)
        self.play_device_choose.addItems(["本机"])
        self.now_time_label.setGraphicsEffect(shadow1)
        progress_layout.addWidget(self.now_time_label)

        
        
        self.progress_bar = QProgressBar(self.left_widget)
        self.progress_bar.setTextVisible(False)
        self.progress_bar.mousePressEvent = self.progress_bar_clicked
        progress_layout.addWidget(self.progress_bar)

        self.total_time_label = QLabel("00:00", self.left_widget)
        self.total_time_label.setStyleSheet("color: white; font-weight: bold;")
        shadow2 = QGraphicsDropShadowEffect()
        shadow2.setBlurRadius(10)
        shadow2.setXOffset(2)
        shadow2.setYOffset(2)
        shadow2.setColor(self.shadowcolor)
        self.total_time_label.setGraphicsEffect(shadow2)
        progress_layout.addWidget(self.total_time_label)
        left_layout.addLayout(progress_layout)  # 进度条布局加入左侧布局
        #self.update_ui_theme()

        # ---------------------- 右侧歌词视图 ----------------------
        self.lyric_view = self.advanced_list_view(self)  # 父对象为主窗口
        # 清除歌词视图额外边距，避免顶部留下空白
        self.lyric_view.setContentsMargins(2,0,0,0)
        self.lyric_view.pressed.connect(self.lyric_view_pressed)
        # 记录歌词基准字号，用于高亮当前行时放大
        base_pt = self.lyric_view.font().pointSize()
        if not base_pt or base_pt <= 0:
            base_pt = 12
        self._lyric_base_font_size = base_pt
        self._last_lyric_index = -1
        

        self.splitter = QSplitter(Qt.Horizontal)  # 水平分割
        self.splitter.setHandleWidth(5)
        self.splitter.addWidget(self.left_widget)  # 左侧容器加入分割器
        self.splitter.addWidget(self.lyric_view)   # 歌词视图加入分割器
        self.splitter.setSizes([700, 300])
        self.splitter.setContentsMargins(2,0, 2, 0)


        # ---------------------- 封面图片（最右侧） ----------------------
        self.image_label = QLabel(self)  # 父对象为主窗口
        self.image_label.setFixedSize(230, 230)  # 固定尺寸
        self.image_label.move(470,0) 
        self.baseboard=QLabel(self)
        self.baseboard.setFixedSize(700,230)
        self.baseboard.move(0,0) 
        baseimage = Image.new("RGBA", (700, 230), (0, 0, 0, 1))
        try:
            buf = io.BytesIO()
            baseimage.save(buf, format='PNG')
            data = buf.getvalue()
            pix = QPixmap()
            if pix.loadFromData(data):
                self.baseboard.setPixmap(pix)
            else:
                # 回退：设置为空（避免抛错）
                self.baseboard.clear()
        except Exception as e:
            print(f"[warn] baseboard image -> pixmap failed: {e}")
            try:
                self.baseboard.clear()
            except:
                pass

        _main_layout.addWidget(self.splitter)  # 分割器（左侧+歌词）加入主布局

        # 关键：无需调用self.setLayout(_main_layout)，因为_main_layout创建时已绑定self
    def change_play_device(self,index):
        print(index)
        if index==-1:
            pass
        elif index==0:
            if self.dlnamode:
                self.soco_device.stop()
            self.dlnamode=False
        else:
            self.dlnamode=True
            self.soco_device=soco.SoCo(list(self.devices)[index-1].ip_address)
            # 启动 http server 只需要一次
            self.play_music()
            try:
                if not getattr(self, '_http_server_started', False):
                    self.start_http_server()
                    self._http_server_started = True
            except Exception:
                pass

            # 初始化上一次 transport 状态，避免切换设备时误判为 STOPPED
            try:
                self._last_soco_transport = self.soco_device.get_current_transport_info().get("current_transport_state")
            except Exception:
                self._last_soco_transport = None
    def update_smtc(self, song_name, artist, cover_bytes):
        self._smtc_updater.type = winsdk.windows.media.MediaPlaybackType.MUSIC
        self._smtc_updater.music_properties.title = song_name
        self._smtc_updater.music_properties.artist = artist

        # 封面处理
        # 当有封面字节且非空时设置缩略图，否则清空缩略图
        if cover_bytes:
            try:
                # 从原始字节创建PIL图片并转换为 JPEG 字节流
                img = Image.open(io.BytesIO(cover_bytes))
                byte_stream = io.BytesIO()
                img.save(byte_stream, format="JPEG")
                image_bytes = byte_stream.getvalue()

                # 转换为 SMTC 可识别的流对象
                stream = winsdk.windows.storage.streams.InMemoryRandomAccessStream()
                writer = winsdk.windows.storage.streams.DataWriter(stream)
                writer.write_bytes(image_bytes)
                writer.store_async().get_results()
                self._smtc_updater.thumbnail = winsdk.windows.storage.streams.RandomAccessStreamReference.create_from_stream(stream)
            except Exception as e:
                print(f"封面处理失败：{e}")
                # 如果设置失败，确保 thumbnail 被清空（如果支持）以避免残留旧图
                try:
                    self._smtc_updater.thumbnail = None
                except Exception:
                    pass
        else:
            # 清空缩略图（优先设置为 None；如果属性不接受 None，则忽略异常）
            try:
                self._smtc_updater.thumbnail = None
            except Exception:
                # 退回方案：写入空字节流（确保 write_bytes 使用有效参数）
                try:
                    stream = winsdk.windows.storage.streams.InMemoryRandomAccessStream()
                    writer = winsdk.windows.storage.streams.DataWriter(stream)
                    writer.write_bytes(b"")
                    writer.store_async().get_results()
                    self._smtc_updater.thumbnail = winsdk.windows.storage.streams.RandomAccessStreamReference.create_from_stream(stream)
                except Exception:
                    pass
        self._smtc_updater.update()
    def fix_std_streams(self):
        if getattr(sys, 'frozen', False) and sys.stdout is None:
            # 创建内存缓冲区作为stdout/stderr
            sys.stdout = io.StringIO()
            sys.stderr = io.StringIO()
    def update_ui_theme(self):
        self.is_dark = self.is_darkmode()
        if self.is_dark:
            self.bg_color = "rgba(40, 40, 40, 100)"
            self.text_color = "rgba(255, 255, 255, 230)"
            self.scroll_bg = "rgba(40, 40, 40, 150)"
            self.scroll_handle = "rgba(100, 100, 100, 150)"
            self.scroll_handle_hover = "rgba(120, 120, 120, 180)"
            # 设置深色模式下的亚克力效果
            self.windowEffect.setAcrylicEffect(int(self.winId()), gradientColor="404040A0")
        else:
            self.bg_color = "rgba(255, 255, 255, 100)"
            self.text_color = "rgba(0, 0, 0, 230)"
            self.scroll_bg = "rgba(240, 240, 240, 100)"
            self.scroll_handle = "rgba(200, 200, 200, 150)"
            self.scroll_handle_hover = "rgba(180, 180, 180, 180)"
            # 设置浅色模式下的亚克力效果  mica效果待定
            if self.effect=="Acrylic":
                self.windowEffect.setAcrylicEffect(int(self.winId()),gradientColor="FFFFFF90")
            elif self.effect=="Aero":
                self.windowEffect.setAeroEffect(int(self.winId()))
            else:
                pass
        
        # 获取 Windows 主题色
        try:
            key = winreg.OpenKey(winreg.HKEY_CURRENT_USER, r"SOFTWARE\Microsoft\Windows\CurrentVersion\Explorer\Accent")
            accent_data = winreg.QueryValueEx(key, "AccentColorMenu")[0]
            # 转换为 RGB 格式
            r = max(0, min(255, accent_data & 0xFF))
            g = max(0, min(255, (accent_data >> 8) & 0xFF))
            b = max(0, min(255, (accent_data >> 16) & 0xFF))
            self.theme_color = f"rgba({r}, {g}, {b}, 150)"
            if self.is_dark:
                r2 = max(0, min(255, (accent_data & 0xFF) - 100))
                g2 = max(0, min(255, ((accent_data >> 8) & 0xFF) - 100))
                b2 = max(0, min(255, ((accent_data >> 16) & 0xFF) - 100))
                self.theme_color2 = f"rgba({r2}, {g2}, {b2}, 150)"
            else:
                r2 = max(0, min(255, (accent_data & 0xFF) + 100))
                g2 = max(0, min(255, ((accent_data >> 8) & 0xFF) + 100))
                b2 = max(0, min(255, ((accent_data >> 16) & 0xFF) + 100))
                self.theme_color2 = f"rgba({r2}, {g2}, {b2}, 150)"
        except:
            # 如果获取失败，使用默认蓝色
            self.theme_color = "rgba(100, 150, 255, 150)"
            self.theme_color2 = "rgba(120, 150, 255, 150)"
        
        # 全局字体样式
        base_style = f"""
            * {{
                font-family: "Microsoft YaHei", "微软雅黑";
            }}
        """
        
        # 列表样式
        self.list_widget.setStyleSheet(f"""
            QListWidget {{
                background-color: {self.bg_color};
                color: {self.text_color};
                border: none;
                border-radius: 5px;
                font-family: "Microsoft YaHei", "微软雅黑";
                font-size: 12px;
            }}
            QListWidget::item:selected {{
                background-color: qlineargradient(x1:0, y1:0 , x2:1 ,y2:0 stop:0 {self.theme_color2} ,stop:1 {self.theme_color});
                color:{self.text_color};
                border: none;
                border-radius: 5px;
            }}
            QListWidget::item:hover {{
                background-color: rgba(80, 80, 80, 80);
            }}
        """)
        # 更详细的分割条样式，分别处理横向/纵向把手并在悬停时使用主题色
        self.splitter.setStyleSheet(f"""
            QSplitter::handle {{
                background-color: rgba(0, 0, 0, 0);
                margin: 0px;
            }}
            QSplitter::handle:horizontal {{
                width: 5px;
            }}
            QSplitter::handle:vertical {{
                height: 5px;
            }}
            QSplitter::handle:hover {{
                background-color: {self.theme_color};
            }}
        """)
        # 滚动条样式
        self.play_device_choose.setStyleSheet(f"""
            QComboBox {{
                background-color: {self.bg_color};
                color: {self.text_color};
                border-radius: 5px;
                padding: 5px;
                font-family: "Microsoft YaHei", "微软雅黑";
                font-size: 12px;
            }}
            QComboBox:hover {{
                background-color: rgba(120, 120, 120, 150);
            }}
            QComboBox::drop-down {{
                background-color: rgba(0, 0, 0, 0);
                border: none;
            }}
            QComboBox QAbstractItemView {{
                background-color: {self.bg_color};
                color: {self.text_color};
                border-radius: 5px;
                padding: 5px;
                font-family: "Microsoft YaHei", "微软雅黑";
                font-size: 12px;
                border: none;
            }}
            QComboBox QAbstractItemView::item:hover {{
                background-color:rgba(255, 255, 255, 0.1);  
                color: {self.text_color};  
                border-radius: 5px;
            }}
            QComboBox QAbstractItemView::item:selected {{
                background-color:  {self.theme_color};
                border: none;
                border-radius: 5px;
            }}
        """)


        scroll_style = f"""
            QScrollBar:vertical {{
                background: {self.scroll_bg};
                width: 8px;
                margin: 0px;
                border-radius: 4px;
            }}
            QScrollBar::handle:vertical {{
                background: {self.scroll_handle};
                min-height: 20px;
                border-radius: 4px;
            }}
            QScrollBar::handle:vertical:hover {{
                background: {self.scroll_handle_hover};
            }}
            QScrollBar::add-line:vertical {{
                height: 0px;
            }}
            QScrollBar::sub-line:vertical {{
                height: 0px;
            }}
            QScrollBar::add-page:vertical, QScrollBar::sub-page:vertical {{
                background: none;
            }}
            /* 水平滚动条 */
            QScrollBar:horizontal {{
                background: {self.scroll_bg};
                height: 8px;
                margin: 0px;
                border-radius: 4px;
            }}
            QScrollBar::handle:horizontal {{
                background: {self.scroll_handle};
                min-width: 20px;
                border-radius: 4px;
            }}
            QScrollBar::handle:horizontal:hover {{
                background: {self.scroll_handle_hover};
            }}
            QScrollBar::add-line:horizontal, QScrollBar::sub-line:horizontal {{
                width: 0px;
            }}
            QScrollBar::add-page:vertical, QScrollBar::sub-page:vertical,
            QScrollBar::add-page:horizontal, QScrollBar::sub-page:horizontal {{
                background: none;
            }}
        """
        add_style = f"""
            QListWidget::item:selected {{
                height:30px;
            }}
        """
        self.list_widget.setStyleSheet(self.list_widget.styleSheet() + scroll_style)
        self.lyric_view.setStyleSheet(self.list_widget.styleSheet() + scroll_style+add_style)
        
        # 按钮样式
        button_style = f"""
            QPushButton {{
                background-color: {self.bg_color};
                color: {self.text_color};
                border: none;
                border-radius: 3px;
                padding: 5px;
                font-family: "Microsoft YaHei", "微软雅黑";
                font-size: 12px;
            }}
            QPushButton:hover {{
                background-color: rgba(120, 120, 120, 150);
            }}
        """
        self.play_button.setStyleSheet(button_style)
        self.hide_show_button.setStyleSheet(button_style)
        self.move_button.setStyleSheet(button_style)
        self.search_button.setStyleSheet(button_style)
        self.change_order_button.setStyleSheet(button_style)

        # 标签样式
        label_style = f"""
            QLabel {{
                color: {self.text_color};
                background: transparent;
                font-family: "consolas","Microsoft YaHei", "微软雅黑";
                font-size: 14px;
            }}
        """
        self.now_time_label.setStyleSheet(label_style)
        self.total_time_label.setStyleSheet(label_style)

        # 进度条样式
        self.progress_bar.setStyleSheet(f"""
            QProgressBar {{
                background-color: {self.bg_color};
                border: none;
                border-radius: 10px;
                font-family: "Microsoft YaHei", "微软雅黑";
                font-size: 12px;
            }}
            QProgressBar::chunk {{
                background-color: {self.theme_color};
                border-radius: 10px;
            }}
        """)

        # 应用全局样式
        self.setStyleSheet(base_style)
    def t_server(self):
            # 1. 用 partial 给处理器绑定 directory 参数
            if self.onlinemode==False:
                Handler = partial(SimpleHTTPRequestHandler, directory=self._playpath)
            elif self.onlinemode:
                Handler = partial(SimpleHTTPRequestHandler, directory=self.online_downloader.download_dir)
                
            # 2. 创建服务器时，传递绑定后的处理器（不再传递 directory 给 HTTPServer）
            self.server = HTTPServer(("0.0.0.0", self.port), Handler)
            try:
                self.server.serve_forever()
            except OSError:
                pass
    def start_http_server(self):
        
        t = threading.Thread(target=self.t_server)
        t.start()
    
    def is_darkmode(self):
        try:
            key = winreg.OpenKey(winreg.HKEY_CURRENT_USER, r"Software\Microsoft\Windows\CurrentVersion\Themes\Personalize")
            d, _ = winreg.QueryValueEx(key, "AppsUseLightTheme")
            winreg.CloseKey(key)
            return d == 0
        except FileNotFoundError:
            return False
            
    def to_now_playing(self):
        self.list_widget.scrollToItem(self.list_widget.item(self.current_index))
        
    def hotkey(self):
        self.hotkey_states = {
            'ctrl+alt+x': False,
            'ctrl+alt+>': False,
            'ctrl+alt+<': False,
            'ctrl+alt+/': False,
            'ctrl+alt+l': False
        }
        hotkeys = [
            ('ctrl+alt+x', self.quit_musicplayer),
            ('ctrl+alt+>', self.next_song),
            ('ctrl+alt+<', self.prev_song),
            ('ctrl+alt+/', self.toggle_play_pause),
            ('ctrl+alt+l', self.hide_show_window)
        ]
        
        for hotkey, action in hotkeys:
            if keyboard.is_pressed(hotkey):
                # 如果按键刚刚按下（之前状态为False）
                if not self.hotkey_states[hotkey]:
                    self.hotkey_states[hotkey] = True
                    # 执行对应的操作
                    action()
                    # 添加短暂延迟，避免连续触发
                    time.sleep(0.3)  # 300ms防抖延迟
            else:
                # 按键释放，重置状态
                self.hotkey_states[hotkey] = False
            
    def init_playlist(self, playpath):
        global lyric_files
        music_files = []
        lyric_files = []
        for name in os.listdir(playpath):
            parts = name.split('.')
            if len(parts) > 1 and (parts[-1].lower() == "mp3" or parts[-1].lower() == "flac"):
                file_path = os.path.join(playpath, name)
                creation_time = os.path.getctime(file_path)
                music_files.append((name, creation_time))
            if len(parts) > 1 and (parts[-1].lower() == "lrc" ):
                # 存储歌词文件的完整路径，避免后续 open 时因工作目录不同导致找不到文件
                lyric_files.append((parts[0], os.path.join(playpath, name)))
            if os.path.isdir(os.path.join(playpath, name)):
                if name in ["lyrics", "Lyrics", "LYRICS", "歌词", "LYRIC", "Lyric"]:
                    lyric_dir = os.path.join(playpath, name)  # 歌词目录的完整路径
                    for lyric_name in os.listdir(lyric_dir):
                        parts = lyric_name.split('.')
                        if len(parts) > 1 and (parts[-1].lower() == "lrc"):
                            lyric_path = os.path.join(lyric_dir, lyric_name)  # 歌词文件的完整路径
                            lyric_files.append((parts[0], lyric_path))  # 存储完整路径而不是文件名
        # 按创建时间倒序排序
        music_files.sort(key=lambda x: x[1], reverse=True)
        # 只保留文件名
        self.playlist = [file[0] for file in music_files]
            
        
    def load_music_playlist(self):#修改json
        # 使用 JSON 配置文件（config.json）存储 music_path
        config_file = Path('config.json')
        self._playpath=""
        # 如果配置文件不存在，弹窗让用户选择音乐目录并创建配置文件
        if not config_file.exists():
            music_path = QFileDialog.getExistingDirectory(self, "请选择音乐文件夹（第一次启动配置）")
            if not music_path:
                # 用户取消选择，弹出警告并返回
                QMessageBox.warning(self, "警告", "未选择音乐文件夹，程序将无法加载播放列表")
                return
            self.cfg = {"music_path": music_path}
            self._playpath = music_path
            try:
                with config_file.open('w', encoding='utf-8') as f:
                    json.dump(self.cfg, f, ensure_ascii=False, indent=2)
            except Exception as e:
                print(f"[warn] 写入配置文件失败: {e}")

        # 读取配置
        try:
            with config_file.open('r', encoding='utf-8') as f:
                self.cfg = json.load(f)
                playpath = self.cfg.get('music_path', '').strip()
                self._playpath = playpath
                try:
                    self.playlistid = self.cfg.get('playlistid', '').strip()
                    if self.playlistid!="":
                        self.onlinemode=True
                except:
                    self.onlinemode=False
                
        except Exception:
            playpath = ''

        try:
            # 创建包含文件名和创建时间的列表
            self.init_playlist(playpath)
        except FileNotFoundError:
            QMessageBox.warning(self, "警告", "路径不存在")
            music_path = QFileDialog.getExistingDirectory(self, "请选择音乐文件夹")
            self._playpath = music_path
            if not music_path:
                return
            try:
                with config_file.open('w', encoding='utf-8') as f:
                    json.dump({"music_path": music_path}, f, ensure_ascii=False, indent=2)
            except Exception as e:
                print(f"[warn] 写入配置文件失败: {e}")
            self.init_playlist(music_path)
            
        self.update_list_widget_offline()
        # 设置当前索引为0（第一首歌）并播放
        if self.playlist:
            self.current_index = 0

    def lyric_view_pressed(self, index):
        # 将 QModelIndex 转换为 QListWidgetItem
        global c
        c1=c
        try:
            if self.dlnamode==False:
                c=(lyrics[index.row()]-pygame.mixer.music.get_pos())
                pygame.mixer.music.set_pos(lyrics[index.row()]/1000)
        except:
            c=c1
    def search(self):
        print("[info] 歌曲搜索")
        # 检查窗口是否已存在且未关闭
        if self.search_window is not None and self.search_window.isVisible():
            self.search_window.raise_()
            self.search_window.activateWindow()
            return
        # 否则新建
        self.search_window = SearchWindow(parent=self)
        self.search_window.show()
        self.search_window.raise_()
        self.search_window.activateWindow()
        
    def search_exec_runner(self, keyword, iscap):
        thread_search = threading.Thread(target=self.search_exec, args=(keyword, iscap))
        thread_search.daemon = True
        self.search_result_index=0
        thread_search.start()
        
    def search_exec(self, keyword, iscap):
        self.search_result=[]
        """根据关键字搜索列表框中的项目"""
        # 清除之前的高亮
        for i in range(self.list_widget.count()):
            item = self.list_widget.item(i)
            item.setBackground(QColor(255, 255, 255, 0))
            QApplication.processEvents()
            if self.quit_flag == 1:
                break
        x=self.list_widget.count()
        # 查找匹配项
        for i in range(self.list_widget.count()):
            item = self.list_widget.item(i)
            if self.quit_flag == 1:
                break
            e=item.text()
            if iscap:
                if keyword.lower() in item.text().replace(".mp3","").replace(".flac","").lower():
                    item.setBackground(QColor(100, 150, 255, 100))
                    self.search_result.append(i)
            else:
                if keyword in item.text().replace(".mp3","").replace(".flac",""):
                    item.setBackground(QColor(100, 150, 255, 100))
                    self.search_result.append(i)
            QApplication.processEvents()
            self.update()
    
    def clear_highlight(self):
        for i in range(self.list_widget.count()):
            item = self.list_widget.item(i)
            item.setBackground(QColor(255, 255, 255, 0))
            time.sleep(0.001)
            if self.quit_flag == 1:
                break
    def update_list_widget_online(self):
        self.list_widget.clear()
        for index, song in enumerate(self.playname, 1):
            if len(song) >= 60:
                song = song[0:60] + "..."
            display_text = f" {song}"
            self.list_widget.addItem(display_text)

    def update_list_widget_offline(self):
        self.list_widget.clear()
        for index, song in enumerate(self.playlist, 1):
            song_name = os.path.basename(song)
            if len(song_name) >= 60:
                song_name = song_name[0:60] + "..."
            display_text = f" {song_name}"
            self.list_widget.addItem(display_text)

    def play_selected_song(self):
            global c
        #try:
            c = 0
            selected_items = self.list_widget.selectedItems()
            if selected_items:
                selected_index = self.list_widget.row(selected_items[0])
                self.current_index = selected_index
                self.play_music()
            '''except Exception as e:
            print(f"选择歌曲错误: {str(e)}")
            msg_box = QMessageBox()
            msg_box.setIcon(QMessageBox.Warning)
            msg_box.setWindowTitle("错误")
            msg_box.setText("选择歌曲时发生错误")
            msg_box.setStandardButtons(QMessageBox.Ok)
            msg_box.setModal(True)
            msg_box.exec_()'''
    def _on_play_pressed(self, sender, args):
        if not self.is_playing:
            self.play_music()
    def _on_pause_pressed(self, sender, args):
        if self.is_playing:
            self.toggle_play_pause()
    def _on_next_pressed(self, sender, args):
        self.next_song()
    def _on_previous_pressed(self, sender, args):
        self.prev_song()
    def change_play_order(self):
        self.playorder=(self.playorder+1)%3
        if self.playorder==0:
            self.change_order_button.setText("顺序播放")
        elif self.playorder==1:
            self.change_order_button.setText("单曲循环")
        elif self.playorder==2:
            self.remain_playlist=self.playlist.copy()
            self.change_order_button.setText("随机播放")
    def get_lyrics_on_file(self,path):
        """
        从本地 .lrc 文件读取歌词，支持多编码回退以避免 UnicodeDecodeError。
        根据传入的音乐文件路径匹配歌词文件名（不含扩展名）。
        返回字符串（读取失败返回 None）。
        """
        path_no_ext = path.replace('.mp3', '').replace(".flac","")

        for entry in lyric_files:
            # lyric_files 中存储为 (name_without_ext, full_path)
            try:
                lyric_path = entry[1]
            except Exception:
                continue

            # 使用 os.path 进行更健壮的文件名比较
            if os.path.splitext(os.path.basename(path_no_ext))[0] == os.path.splitext(os.path.basename(lyric_path))[0]:
                try:
                    with open(lyric_path, 'rb') as f:
                        raw = f.read()

                    # 依次尝试常见编码
                    for enc in ('utf-8-sig', 'utf-8', 'gbk', 'gb2312', 'cp1252', 'latin-1', 'utf-16'):
                        try:
                            lyrics_f = raw.decode(enc)
                            return lyrics_f
                        except Exception:
                            continue

                    # 最后保底：使用 replace 模式避免抛出
                    try:
                        lyrics_f = raw.decode('utf-8', errors='replace')
                        return lyrics_f
                    except Exception as e:
                        print(f"[warn] 最终解码失败: {lyric_path} -> {e}")
                        return None
                except Exception as e:
                    print(f"[warn] 读取歌词失败: {lyric_path} -> {e}")
                    return None

        return None
            
    def get_lyrics(self, path):
        try:
            # 加载 MP3 文件的 ID3 标签
            if path.endswith(".mp3"):
                audio = ID3(path)
                
                # 查找 USLT 帧（歌词帧）
                # USLT 帧可能有多个（不同语言），这里取第一个
                for frame in audio.values():
                    if isinstance(frame, USLT):
                        # frame.text 即为歌词内容
                        # frame.lang 是语言代码（如 'eng' 表示英文）
                        # frame.description 是描述（通常为空）
                        return frame.text
                
                # 若没有 USLT 帧，返回无歌词
                return self.get_lyrics_on_file(path)
            elif path.endswith(".flac"):
                audio = FLAC(path)
                
                # 查找 USLT 帧（歌词帧）
                # USLT 帧可能有多个（不同语言），这里取第一个
                for frame in audio.values():
                    if isinstance(frame, USLT):
                        # frame.text 即为歌词内容
                        # frame.lang 是语言代码（如 'eng' 表示英文）
                        # frame.description 是描述（通常为空）
                        return frame.text
                
                # 若没有 USLT 帧，返回无歌词
                return self.get_lyrics_on_file(path)
        except:
            return self.get_lyrics_on_file(path)
    
    def process_album_art_fast(self, image_data, output_size=(230, 230)):
        """
        快速版本：使用预计算和批量操作
        调整顺序：先进行 alpha 通道处理，再进行模糊操作
        """
        # 打开和预处理图片
        if isinstance(image_data, str):
            img = Image.open(image_data)
        elif isinstance(image_data, bytes):
            img = Image.open(io.BytesIO(image_data))
        elif isinstance(image_data, Image.Image):
            img = image_data
        else:
            raise ValueError("不支持的图片数据类型")

        if img.mode != 'RGBA':
            img = img.convert('RGBA')

        img = img.resize(output_size, Image.Resampling.LANCZOS)
        width, height = img.size

        try:
            # 第一步：先添加 alpha 渐变
            MIN_ALPHA = 0  # 左侧最小不透明值（0-255），可调整
            GRADIENT_FRAC = 1.0
            gradient_end = int(width * GRADIENT_FRAC)
            
            if gradient_end <= 0:
                alpha_mask = Image.new('L', (width, height), 255)
            else:
                row = Image.new('L', (width, 1))
                for x in range(width):
                    if x <= gradient_end:
                        frac = x / gradient_end
                        alpha = int(frac * (255 - MIN_ALPHA) + MIN_ALPHA)
                    else:
                        alpha = 255
                    row.putpixel((x, 0), alpha)
                alpha_mask = row.resize((width, height), Image.Resampling.BILINEAR)

            # 应用 alpha 通道到原图
            img_with_alpha = img.copy()
            img_with_alpha.putalpha(alpha_mask)

            # 第二步：生成两层不同强度的模糊图像
            STRONG_BLUR = 100
            WEAK_BLUR = 0
            
            # 对带有 alpha 通道的图像进行模糊
            blurred_strong = img_with_alpha.filter(ImageFilter.GaussianBlur(STRONG_BLUR))
            blurred_weak = img_with_alpha.filter(ImageFilter.GaussianBlur(WEAK_BLUR))

            # 转为 numpy 数组并归一化到 [0,1]
            arr_strong = np.asarray(blurred_strong).astype(np.float32) / 255.0
            arr_weak = np.asarray(blurred_weak).astype(np.float32) / 255.0

            # 根据 x 位置创建平滑的混合权重
            xs = np.linspace(0.0, 1.0, width, dtype=np.float32)
            weight_strong = np.power(1.0 - xs, 1.6).reshape((1, width, 1))

            # 将权重扩展到高度并混合两幅图像
            weight_strong = np.repeat(weight_strong, height, axis=0)
            arr_blended = arr_strong * weight_strong + arr_weak * (1.0 - weight_strong)

            # 转回 uint8 图像
            arr_out = np.clip(arr_blended * 255.0, 0, 255).astype(np.uint8)
            result = Image.fromarray(arr_out, mode='RGBA')
            #再来一次alpha通道处理
            # 应用 alpha 通道到结果图
            result_with_alpha = result.copy()
            result_with_alpha.putalpha(alpha_mask)
            return result_with_alpha
            
        except Exception as e:
            # 退回到简单的整体模糊并添加 alpha 渐变，保证不会抛出
            print(f"[warn] smooth blur failed, fallback: {e}")
            try:
                # 备用方案：先添加 alpha 渐变，再进行较弱的整体模糊
                MIN_ALPHA = 120
                GRADIENT_FRAC = 0.7
                gradient_end = int(width * GRADIENT_FRAC)
                
                if gradient_end <= 0:
                    alpha_mask = Image.new('L', (width, height), 255)
                else:
                    row = Image.new('L', (width, 1))
                    for x in range(width):
                        if x <= gradient_end:
                            frac = x / gradient_end
                            alpha = int(frac * (255 - MIN_ALPHA) + MIN_ALPHA)
                        else:
                            alpha = 255
                        row.putpixel((x, 0), alpha)
                    alpha_mask = row.resize((width, height), Image.Resampling.BILINEAR)

                # 应用 alpha 通道并进行模糊
                img_with_alpha = img.copy()
                img_with_alpha.putalpha(alpha_mask)
                
                FALLBACK_BLUR = 50
                fallback = img_with_alpha.filter(ImageFilter.GaussianBlur(FALLBACK_BLUR))
                return fallback
                
            except Exception:
                return img
    def play_songs(self):
        global lyrics_lines, lyrics, downloading
        lyric_list = []
        
        # 添加线程锁防止并发下载
        if not hasattr(self, 'download_lock'):
            self.download_lock = threading.Lock()
        
        # 使用锁来确保同一时间只有一个下载进行
        with self.download_lock:
            if downloading:
                print(f"下载已在进行中，跳过重复调用")
                return
            
            if 0 <= self.current_index < len(self.playlist):
                ishaveimg = False
                self.artist = ""
                self.title = ""
                music_folder = self.get_playpath()
                
                if self.onlinemode == False:
                    self.current_song = os.path.join(music_folder, self.playlist[self.current_index])
                else:
                    if hasattr(self, 'current_song_path') and self.current_song_path:
                        self.current_song = self.current_song_path
                    else:
                        # 直接下载，设置下载标志
                        downloading = True
                        try:
                            print(f"开始下载: {self.playid[self.current_index]}")
                            path, online_lyric = self.online_downloader.download(self.playid[self.current_index])
                            self.current_song_path = path
                            self.current_song = path
                            self.online_download_map[self.playid[self.current_index]] = path
                            print(f"下载完成: {path}")
                        except Exception as e:
                            print(f"下载失败: {e}")
                            self.current_index+=1
                            downloading = False
                            return
                        finally:
                            downloading = False
                
                # 其他代码保持不变...
                lyrics = self.get_lyrics(self.current_song)
                if lyrics == None:
                    lyrics = []
                else:
                    lyrics_lines = lyrics.split("\n")
                
                self.lyric_view.clear()
                lyrics, lyric_list = self.parse_lrc(lyrics)
                if self.onlinemode:
                    lyrics, lyric_list = self.parse_lrc(online_lyric)
                print(f"正在播放: {self.current_song}")
                
                # 这里放置图片...
                if self.current_song.endswith(".mp3"):
                    audio = ID3(self.current_song)
                elif self.current_song.endswith(".flac"):
                    audio = FLAC(self.current_song)
                
                album_image_original = None
                try:
                    for tag in audio.values():
                        if isinstance(tag, APIC):
                            album_image_original = tag.data
                            # 处理为 PIL.Image
                            pil_img = self.process_album_art_fast(album_image_original)
                            ishaveimg = True
                            try:
                                # 将 PIL.Image 保存为 PNG 字节，然后由 QPixmap 从数据加载
                                buf = io.BytesIO()
                                pil_img.save(buf, format='PNG')
                                data = buf.getvalue()
                                pixmap = QPixmap()
                                if pixmap.loadFromData(data):
                                    # 保留对 pixmap 的引用，避免被垃圾回收导致显示问题
                                    self._current_album_pixmap = pixmap
                                    self.image_label.setPixmap(pixmap)
                                else:
                                    print("[warn] pixmap.loadFromData failed")
                                    self.image_label.clear()
                            except Exception as e:
                                print(f"[warn] album art conversion failed: {e}")
                                self.image_label.clear()
                            break
                        if isinstance(tag, Picture):
                            album_image_original = tag.data
                            # 处理为 PIL.Image
                            pil_img = self.process_album_art_fast(album_image_original)
                            ishaveimg = True
                            try:
                                # 将 PIL.Image 保存为 PNG 字节，然后由 QPixmap 从数据加载
                                buf = io.BytesIO()
                                pil_img.save(buf, format='PNG')
                                data = buf.getvalue()
                                pixmap = QPixmap()
                                if pixmap.loadFromData(data):
                                    # 保留对 pixmap 的引用，避免被垃圾回收导致显示问题
                                    self._current_album_pixmap = pixmap
                                    self.image_label.setPixmap(pixmap)
                                else:
                                    print("[warn] pixmap.loadFromData failed")
                                    self.image_label.clear()
                            except Exception as e:
                                print(f"[warn] album art conversion failed: {e}")
                                self.image_label.clear()
                            break
                    if not ishaveimg:
                        self.image_label.clear()
                        album_image_original = None
                except:
                    self.image_label.clear()
                    album_image_original = None
                
                for line in lyric_list:
                    self.lyric_view.addItem(line)
                
                if pygame.mixer.music.get_busy():
                    pygame.mixer.music.stop()
                
                if self.current_song.endswith(".mp3"):
                    try:
                        self.title = audio["TIT2"][0]
                    except:
                        pass
                    try:
                        self.artist = "&".join(audio["TPE1"])
                    except:
                        pass
                
                if self.current_song.endswith(".flac"):
                    try:
                        self.title = audio["title"][0]
                    except:
                        pass
                    try:
                        self.artist = "&".join(audio["artist"])
                    except:
                        pass
                
                try:
                    if self.title == "":
                        self.title = self.playlist[self.current_index].split("-")[0]
                    if self.artist == "":
                        self.title = self.playlist[self.current_index].split("-")[1].split(".")[0]
                except:
                    if "." in str(self.playlist[self.current_index]):
                        self.title = self.playlist[self.current_index].split(".")[0]
                    else:
                        self.title = self.playlist[self.current_index]
                
                if self.dlnamode:
                    if self.onlinemode==False:
                        uncodedurl = f"http://{self.myip}:{self.port}/" + (self.playlist[self.current_index])
                    elif self.onlinemode:
                        uncodedurl = f"http://{self.myip}:{self.port}/" + (self.online_download_map[self.playid[self.current_index]]).split("\\")[-1]
                    url = parse.quote(uncodedurl, safe=":/")
                    print(url)
                    self.soco_device.play_uri(url)
                    # 初始化/刷新 transport state，避免刚调用 play_uri 时被误判为 STOPPED
                    try:
                        self._last_soco_transport = self.soco_device.get_current_transport_info().get("current_transport_state")
                    except Exception:
                        self._last_soco_transport = None
                else:
                    pygame.mixer.music.load(self.current_song)
                    pygame.mixer.music.play()
                
                self.is_playing = True
                self.play_button.setText("暂停")
                self.list_widget.setCurrentRow(self.current_index)
                
                if album_image_original == None:
                    album_image_original = b""
                
                try:
                    self.update_smtc(self.title, self.artist, album_image_original)
                except:
                    pass
                
                # 重置音乐时长，让refresh_ui重新计算
                self.music_long = 0
            
            
    def play_music(self):
        global lyric_index
        if not self.playlist:
            return
            
        if hasattr(self, 'current_song_path'):
            delattr(self, 'current_song_path')
            
        '''try:'''
        self.play_songs()
        if self.smtc_available:
            self._smtc.playback_status = winsdk.windows.media.MediaPlaybackStatus.PLAYING
        lyric_index = 0
        '''except Exception as e:
            for i in range(5):
                print("[warn] 播放错误，正在重试...")
                try:
                    self.play_songs()
                    break
                except:
                    pass
                time.sleep(1)
            else:
                print(f"播放错误: {str(e)}")
                msg_box = QMessageBox()
                msg_box.setIcon(QMessageBox.Warning)
                msg_box.setWindowTitle("错误")
                msg_box.setText(f"无法播放当前歌曲: {str(e)}")
                msg_box.setStandardButtons(QMessageBox.Ok)
                msg_box.setModal(True)
                msg_box.exec_()'''

    def auto_play_next_song(self):
        """统一自动下一首逻辑"""
        # 无播放列表直接返回
        if not self.playlist:
            return
        print(downloading)
        if downloading:
            print("！！！！！！！！！！！！！！！！！！！！！！！！！！！！！在下载！！！！！！！！！！！！！！！！！！！！！！")
            return
        # 计算下一首索引
        if self.playorder == 0:  # 顺序播放
            next_index = (self.current_index + 1) % len(self.playlist)
        elif self.playorder == 1:  # 单曲循环
            next_index = self.current_index
        elif self.playorder == 2:  # 随机播放
            if not self.remain_playlist:
                self.remain_playlist = self.playlist.copy()
            # 移除当前歌曲时先校验是否存在
            if self.playlist[self.current_index] in self.remain_playlist:
                self.remain_playlist.remove(self.playlist[self.current_index])
            # 防止空列表报错
            if not self.remain_playlist:
                self.remain_playlist = self.playlist.copy()
            next_song = random.choice(self.remain_playlist)
            next_index = self.playlist.index(next_song)
        
        # 更新索引
        self.current_index = next_index
        global c
        c = 0
        
        # 触发播放
        try:
            self.play_request.emit()
        except Exception:
           # self.play_music()
           pass
    def get_playpath(self):
        config_file = Path('config.json')
        try:
            with config_file.open('r', encoding='utf-8') as f:
                self.cfg = json.load(f)
                return self.cfg.get('music_path', '').strip()
        except Exception:
            return ''
    def parse_lrc(self,lrc_content: str):
        """
        解析LRC文件格式
        
        Args:
            lrc_content: LRC文件内容字符串
            
        Returns:
            Tuple[List[int], List[str]]: (时间列表(毫秒), 歌词列表)
        """
        # 存储解析结果
        if lrc_content==[]:
            return [],[]
        time_list = []
        lyric_list = []
        
        # 存储元数据
        metadata = {}
        
        # 正则表达式匹配时间标签和歌词
        time_pattern = re.compile(r'\[(\d+):(\d+)\.?(\d+)?\](.*)')
        # 正则表达式匹配元数据标签
        metadata_pattern = re.compile(r'\[(ti|ar|al|by|offset):(.*)\]', re.I)
        
        lines = lrc_content.strip().split('\n')
        
        for line in lines:
            line = line.strip()
            if not line:
                continue
                
            # 检查是否是元数据标签
            metadata_match = metadata_pattern.match(line)
            if metadata_match:
                tag_type = metadata_match.group(1).lower()
                tag_value = metadata_match.group(2).strip()
                metadata[tag_type] = tag_value
                continue
                
            # 检查是否是时间标签
            time_match = time_pattern.match(line)
            if time_match:
                minutes = int(time_match.group(1))
                seconds = int(time_match.group(2))
                milliseconds = int(time_match.group(3)) if time_match.group(3) else 0
                
                # 处理毫秒位数（可能是2位或3位）
                if time_match.group(3):
                    if len(time_match.group(3)) == 2:  # 百分秒
                        milliseconds = milliseconds * 10
                    # 如果是3位，已经是毫秒，不需要转换
                
                # 计算总毫秒数
                total_ms = (minutes * 60 + seconds) * 1000 + milliseconds
                
                lyric = time_match.group(4).strip()
                
                # 只添加有歌词的时间点
                if lyric:
                    time_list.append(total_ms)
                    lyric_list.append(lyric)
        
        # 处理偏移量（如果有）
        if 'offset' in metadata:
            try:
                offset = int(metadata['offset'])
                time_list = [max(0, time + offset) for time in time_list]
            except ValueError:
                pass  # 如果offset不是有效数字，忽略
        
        return time_list, lyric_list


    def toggle_play_pause(self):
        if not self.playlist:
            return
            
        if self.is_playing:
            if self.dlnamode==True:
                self.soco_device.pause()
            else:
                pygame.mixer.music.pause()
            self.is_playing = False
            self.play_button.setText("播放")  # 修复按钮文字显示
            if self.smtc_available:
                self._smtc.playback_status = winsdk.windows.media.MediaPlaybackStatus.PAUSED
        else:
            if self.dlnamode==True:
                self.soco_device.play()
            else:
                pygame.mixer.music.unpause()
            self.is_playing = True
            self.play_button.setText("暂停")  # 修复按钮文字显示
            if self.smtc_available:
                self._smtc.playback_status = winsdk.windows.media.MediaPlaybackStatus.PLAYING

    def prev_song(self):
        global c
        if not self.playlist:
            return
            
        c = 0
        self.current_index = (self.current_index - 1) % len(self.playlist)
        self.play_music()

    def next_song(self):
        global c
        if not self.playlist:
            return
            
        c = 0
        self.current_index = (self.current_index + 1) % len(self.playlist)
        self.play_music()

    def hide_show_window(self):
        # 使用滑动动画从屏幕左侧显示/隐藏窗口
        if self.window_position=="left":
            on_x=self.primary_screen.x()
            off_x=self.primary_screen.x()-self.width()
        else:
            on_x=self.primary_screen.width()-self.width()
            off_x=self.primary_screen.width()
        current_y = self.y()

        # 如果正在执行动画，则忽略额外请求
        if getattr(self, '_anim_running', False):
            return

        # 显示窗口（从屏外滑入并淡入）
        if self.show_flag == 0:
            # 记录上次目标位置以便隐藏后恢复
            self._last_pos = QPoint(on_x, current_y)
            # 先将窗口放到屏幕外右侧，然后 show()
            self.move(off_x, current_y)
            # 先把窗口透明度置为0以便淡入
            try:
                self.setWindowOpacity(0.0)
            except Exception:
                pass
            self.show()

            # 位置动画
            anim_pos = QPropertyAnimation(self, b"pos")
            anim_pos.setDuration(350)
            anim_pos.setStartValue(QPoint(off_x, current_y))
            anim_pos.setEndValue(QPoint(on_x, current_y))
            anim_pos.setEasingCurve(QEasingCurve.OutCubic)

            # 透明度动画（淡入）
            anim_opacity = QPropertyAnimation(self, b"windowOpacity")
            anim_opacity.setDuration(350)
            anim_opacity.setStartValue(0.0)
            anim_opacity.setEndValue(1.0)
            anim_opacity.setEasingCurve(QEasingCurve.OutCubic)

            # 并行动画组
            group = QParallelAnimationGroup(self)
            group.addAnimation(anim_pos)
            group.addAnimation(anim_opacity)

            def on_finished_show():
                self._anim_running = False
                self._anim = None
                self._anim_group = None
                self.show_flag = 1

            self._anim_running = True
            self._anim = anim_pos
            self._anim_group = group
            group.finished.connect(on_finished_show)
            group.start()
        else:
            # 隐藏窗口（向屏外滑出并淡出）
            start_x = self.x()
            anim_pos = QPropertyAnimation(self, b"pos")
            anim_pos.setDuration(300)
            anim_pos.setStartValue(QPoint(start_x, current_y))
            anim_pos.setEndValue(QPoint(off_x, current_y))
            anim_pos.setEasingCurve(QEasingCurve.InCubic)

            # 透明度动画（淡出）
            anim_opacity = QPropertyAnimation(self, b"windowOpacity")
            anim_opacity.setDuration(300)
            # 从当前不透明值开始到 0
            try:
                current_op = self.windowOpacity()
            except Exception:
                current_op = 1.0
            anim_opacity.setStartValue(current_op)
            anim_opacity.setEndValue(0.0)
            anim_opacity.setEasingCurve(QEasingCurve.InCubic)

            group = QParallelAnimationGroup(self)
            group.addAnimation(anim_pos)
            group.addAnimation(anim_opacity)

            def on_finished_hide():
                self._anim_running = False
                self.hide()
                # 恢复不透明度，便于下次显示时先设置为0再播放淡入动画
                try:
                    self.setWindowOpacity(1.0)
                except Exception:
                    pass
                self._anim = None
                self._anim_group = None
                self.show_flag = 0

            self._anim_running = True
            self._anim = anim_pos
            self._anim_group = group
            group.finished.connect(on_finished_hide)
            group.start()

    def start_progress_update(self):
        update_thread = threading.Thread(target=self.update_progress)
        update_thread.daemon = True
        update_thread.start()

    def update_progress(self):
        global c
        while True:
            if self.quit_flag == 1:
                break
                # 
            if self.is_playing and self.dlnamode==False:
                current_pos = pygame.mixer.music.get_pos()
                self.progress_update_signal.emit(current_pos, self.music_long)
                #print(current_pos,self.music_long,pygame.mixer.music.get_pos(),c,pygame.mixer.music.get_pos()+c)
                if  self.playlist and self.dlnamode==False and (not downloading) and (pygame.mixer.music.get_pos()+c>=(self.music_long)-100) and self.music_long>0:#防止误差
                    self.auto_play_next_song()
                #少放0.1s应该没有问题吧......
            if self.dlnamode==True:
                self.now_time_label.setText("STREAMING")
                try:
                    self.total_time_label.setText(f"Vol: {self.soco_device.volume}")
                except:
                    self.dlnamode=False

                self.progress_bar.setValue(self.soco_device.volume)
            if self.is_playing and self.dlnamode==True:
                try:
                    state = self.soco_device.get_current_transport_info().get("current_transport_state")
                except Exception:
                    state = None

                # 仅在 transport state 从非 STOPPED 变为 STOPPED 时触发下一首，防止在切换设备或查询期间重复触发
                if state == "STOPPED" and self._last_soco_transport != "STOPPED":
                    time.sleep(0.5)  # 延迟触发
                    self.auto_play_next_song()

                # 更新上一次状态
                self._last_soco_transport = state
            time.sleep(0.1)

    def start_music_thread(self):
        music_thread = threading.Thread(target=self.control_music)
        music_thread.daemon = True
        music_thread.start()

    def control_music(self):
        # 等待初始化完成
        time.sleep(1)
        if self.playlist:
            # 通过信号在主线程执行播放，避免后台线程直接操作 GUI
            try:
                self.play_request.emit()
            except Exception:
                # 退回到直接调用（极端情况下）
                self.play_music()

    def mousePressEvent(self, event):
        if event.button() == Qt.LeftButton:
            # 检查鼠标点击的位置是否在子控件上
            child = self.childAt(event.pos())
            # 始终接受事件，防止事件透传到窗口下方的其他应用
            event.accept()

            # 只有在点击空白区或非交互性的 QLabel（例如背景/baseboard）时允许拖动
            if (child is None) or isinstance(child, QLabel) or child == getattr(self, 'baseboard', None):
                self.drag_position = event.globalPos() - self.frameGeometry().topLeft()
                return

    def mouseMoveEvent(self, event):
        if hasattr(self, 'drag_position') and event.buttons() == Qt.LeftButton:
            # 计算目标左上角位置（基于初始 drag_position）
            new_top_left = event.globalPos() - self.drag_position

            # 使用屏幕矩形进行夹取(clamp)，避免窗口超出屏幕范围
            screen_rect = self.primary_screen  # 已在 init_ui 中设置为 availableGeometry()

            min_x = screen_rect.x()
            max_x = screen_rect.x() + screen_rect.width() - self.width()
            min_y = screen_rect.y()
            max_y = screen_rect.y() + screen_rect.height() - self.height()

            # 夹取 new_top_left 的坐标
            clamped_x = max(min_x, min(new_top_left.x(), max_x))
            clamped_y = max(min_y, min(new_top_left.y(), max_y))

            # 靠近边缘时自动吸附（snap）——减少误差阈值
            snap_threshold = 30
            if abs(clamped_x - min_x) <= snap_threshold:
                clamped_x = min_x
            elif abs(max_x - clamped_x) <= snap_threshold:
                clamped_x = max_x

            # 根据窗口水平中心判断停靠方向（左/右）
            center_x = clamped_x + (self.width() / 2)
            screen_center_x = screen_rect.x() + (screen_rect.width() / 2)
            self.window_position = "left" if center_x <= screen_center_x else "right"

            # 最终移动窗口到夹取后的位置（即时移动以保持拖动流畅）
            self.move(int(clamped_x), int(clamped_y))
            event.accept()
    def smoothMoveEdge(self):
        screen_rect = self.primary_screen
        min_x = screen_rect.x()
        max_x = screen_rect.x() + screen_rect.width() - self.width()

        # 选择最近的边缘作为目标
        cur_x = self.x()
        target_x = min_x if abs(cur_x - min_x) <= abs(cur_x - max_x) else max_x
        self.window_position = 'left' if target_x == min_x else 'right'

        # 使用动画平滑贴靠
        anim = QPropertyAnimation(self, b"pos")
        anim.setDuration(150)
        anim.setStartValue(self.pos())
        anim.setEndValue(QPoint(int(target_x), int(self.y())))
        anim.setEasingCurve(QEasingCurve.OutCubic)
        anim.start()
        # 保留引用避免被回收
        self._snap_anim = anim
    def mouseReleaseEvent(self, event):
        # 在释放鼠标时，带动画将窗口贴靠到最近的左右屏幕边缘
        if event.button() == Qt.LeftButton and hasattr(self, 'drag_position'):
            try:
                self.smoothMoveEdge()
            except Exception:
                pass

            # 清理拖动状态
            try:
                del self.drag_position
            except Exception:
                pass

            event.accept()
        else:
            super().mouseReleaseEvent(event)
    def nativeEvent(self, eventType, message):
        # 只在Windows上处理
        if eventType == "windows_generic_MSG":
            msg = ctypes.wintypes.MSG.from_address(message.__int__())
            WM_SETTINGCHANGE = 0x001A
            WM_MOVING = 0x0216
            WM_EXITSIZEMOVE = 0x0232

            # 主题变化处理（保持原逻辑）
            if msg.message == WM_SETTINGCHANGE:
                if msg.lParam and ctypes.cast(msg.lParam, ctypes.c_wchar_p).value == "ImmersiveColorSet":
                    self.update_ui_theme()
                    return True, 0

            # 在窗口被系统拖动时（实时）——修改传入的 RECT，而不是在 Qt 层反复 move/动画
            if msg.message == WM_MOVING:
                # 延迟定义 RECT 以避免全局污染
                class RECT(ctypes.Structure):
                    _fields_ = [
                        ('left', ctypes.wintypes.LONG),
                        ('top', ctypes.wintypes.LONG),
                        ('right', ctypes.wintypes.LONG),
                        ('bottom', ctypes.wintypes.LONG),
                    ]

                try:
                    rect_ptr = ctypes.cast(msg.lParam, ctypes.POINTER(RECT))
                    rect = rect_ptr.contents

                    w = rect.right - rect.left
                    h = rect.bottom - rect.top

                    # 使用初始化时缓存的可用屏幕矩形
                    screen_rect = self.primary_screen
                    snap_distance = 10

                    # 左贴边
                    if abs(rect.left - screen_rect.x()) <= snap_distance:
                        rect.left = screen_rect.x()
                        rect.right = rect.left + w
                    # 顶贴边
                    if abs(rect.top - screen_rect.y()) <= snap_distance:
                        rect.top = screen_rect.y()
                        rect.bottom = rect.top + h
                    # 右贴边
                    screen_right = screen_rect.x() + screen_rect.width()
                    if abs(rect.right - screen_right) <= snap_distance:
                        rect.right = screen_right
                        rect.left = rect.right - w
                    # 底贴边
                    screen_bottom = screen_rect.y() + screen_rect.height()
                    if abs(rect.bottom - screen_bottom) <= snap_distance:
                        rect.bottom = screen_bottom
                        rect.top = rect.bottom - h

                    # 将修改回写到系统传入的 RECT（系统会使用修改后的矩形来移动窗口）
                    rect_ptr.contents = rect

                    # 更新内部方向状态，但不要在拖动过程中触发动画或再次 move()
                    center_x = rect.left + (w / 2)
                    screen_center_x = screen_rect.x() + (screen_rect.width() / 2)
                    self.window_position = "left" if center_x <= screen_center_x else "right"

                    return True, 0
                except Exception:
                    # 如果处理失败，回落到默认处理
                    return super().nativeEvent(eventType, message)

            # 鼠标释放/结束系统移动时，使用平滑动画完成贴靠（避免在每帧都创建动画）
            if msg.message == WM_EXITSIZEMOVE:
                try:
                    self.smoothMoveEdge()
                except Exception:
                    pass
                return True, 0
        return super().nativeEvent(eventType, message)
    def refresh_ui(self):
        global lyric_index, is_scrolling, no_scroll_event
        try:
            if self.is_playing and pygame.mixer.music.get_busy() and self.playlist and not self.dlnamode:
                a = pygame.mixer.music.get_pos()
                current_pos = a + c
                #self.list_widget.setCurrentRow(self.current_index)
                lyric_index = bisect.bisect_left(lyrics, current_pos) - 1
                
                # 夹取索引范围，避免越界
                if lyric_index < 0:
                    lyric_index = 0
                elif lyric_index >= self.lyric_view.count():
                    lyric_index = self.lyric_view.count() - 1

                # 更新选择并居中当前行
                self.lyric_view.setCurrentRow(lyric_index)
                
                item = self.lyric_view.item(lyric_index)
                if item:
                    # 恢复上一个高亮行的字体
                    prev_idx = getattr(self, '_last_lyric_index', -1)
                    if prev_idx is not None and prev_idx != -1 and prev_idx != lyric_index:
                        try:
                            prev_item = self.lyric_view.item(prev_idx)
                            if prev_item:
                                f_prev = QFont("微软雅黑")
                                f_prev.setBold(False)
                                f_prev.setPointSize(self._lyric_base_font_size)
                                prev_item.setFont(f_prev)
                        except Exception:
                            pass

                    # 设置当前行为加粗并放大
                    try:
                        font = QFont("等线", 16)
                        f = font
                        f.setBold(True)
                        item.setFont(f)
                    except Exception:
                        pass

                    # 只有在用户没有手动滚动时才自动滚动到当前歌词t)
                    
                    if no_scroll_event > 10:
                        self.lyric_view.scrollToItem(item, QAbstractItemView.PositionAtCenter)
                    else:
                        no_scroll_event += 1                     

                    self._last_lyric_index = lyric_index

                # 确保current_pos不超过总时长
                if self.music_long > 0 and current_pos > self.music_long:
                    current_pos = self.music_long
                
                # 发送信号到主线程更新UI
                self.update_ui_signal.emit(current_pos, self.music_long)
                
                # 首次获取总时长
                if self.music_long == 0:
                    try:
                        music_folder = self.get_playpath()
                        if self.onlinemode==False:
                            self.current_song = os.path.join(music_folder, self.playlist[self.current_index])
                        audio = pygame.mixer.Sound(self.current_song)
                        self.music_long = int(audio.get_length() * 1000)
                        self.update_ui_signal.emit(current_pos, self.music_long)
                    except Exception as e:
                        print(f"[warn] 获取音乐时长失败: {str(e)}")
            elif self.is_playing and not pygame.mixer.music.get_busy() and not self.dlnamode:
                # 播放结束但未切换歌曲时，强制更新进度条到100%
                if self.music_long > 0:
                    self.update_ui_signal.emit(self.music_long, self.music_long)
            elif self.is_playing and self.dlnamode:
                volume = self.soco_device.volume
                self.update_ui_signal.emit(volume, 10)

        except Exception as e:
            print(f"[warn] refresh_ui error: {e}")
    lyric_index=0
    def update_ui_handler(self, current_pos, total_pos):
        global lyric_index
        """主线程中处理UI更新（关键修复：确保此函数被正确调用）"""
        # 更新当前时间标签
        if not self.dlnamode:
            minutes = current_pos // 60000
            seconds = (current_pos % 60000) // 1000

            self.now_time_label.setText(f"{minutes:02d}:{seconds:02d}")
            


            # 更新进度条
            if total_pos > 0:
                self.progress_bar.setMaximum(total_pos)
                self.progress_bar.setValue(current_pos)
                self.progress_bar.update() 
            # 更新总时间标签
            if total_pos > 0:
                total_minutes = total_pos // 60000
                total_seconds = (total_pos % 60000) // 1000
                self.total_time_label.setText(f"{total_minutes:02d}:{total_seconds:02d}")
        if self.dlnamode:
            self.progress_bar.setMaximum(100)
            self.progress_bar.setValue(self.soco_device.volume)
            self.progress_bar.update()

    def closeEvent(self, event):
        """窗口关闭时清理资源"""
        self.quit_flag = 1
        pygame.mixer.quit()
        window_x=self.pos().x()
        window_y=self.pos().y()
        try:
            self.server.server_close()
        except:
            pass
        #self.cfg["x"]=window_x
        #self.cfg["y"]=window_y
        """
        with open("config.json","w") as f:
            json.dump(self.cfg,f)"""
        event.accept()

    def progress_bar_clicked(self, event):
        # 计算点击位置对应的音乐时间
        global c
        if not self.dlnamode:
            if self.music_long <= 0:
                return
                
            width = self.progress_bar.width()
            x = event.x()
            ratio = x / width
            target_time = int(self.music_long * ratio)
            c = target_time - pygame.mixer.music.get_pos()
            
            try:
                # 设置音乐播放位置（毫秒转换为秒）
                pygame.mixer.music.set_pos(target_time / 1000.0)
                
                # 立即更新UI
                self.update_ui_signal.emit(target_time + c, self.music_long)
            except Exception as e:
                print(f"设置播放位置失败: {str(e)}")
        else:
            width = self.progress_bar.width()
            x = event.x()
            ratio = x / width
            volume = ratio * 100
            if volume>=self.maxvol:
                msg = QMessageBox()
                msg.setIcon(QMessageBox.Information)
                msg.setText(f"音量设置为{self.maxvol}以上可能会导致音量过高，是否继续？")
                msg.setWindowTitle("音量警告")
                msg.setStandardButtons(QMessageBox.Yes | QMessageBox.No)
                ret = msg.exec_()
                if ret == QMessageBox.No:
                    return
            self.soco_device.volume=volume
    def next_item(self):
        if self.search_result==[]:
            return 
        self.search_result_index+=1
        if self.search_result_index>=len(self.search_result):
            self.search_result_index=0
        self.list_widget.scrollTo(self.list_widget.model().index(self.search_result[self.search_result_index], 0))

class SearchWindow(QWidget):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.parent_player = parent  # 保存主窗口引用
        self.initUI()
        self.update_ui_theme()
     
    def initUI(self):
        # 设置窗口属性
        self.setWindowTitle("搜索窗口")
        self.setWindowFlags(Qt.Window |Qt.CustomizeWindowHint | Qt.WindowTitleHint | Qt.WindowStaysOnTopHint)
        self.setGeometry(400, 400,300,100)
        
        # 创建布局
        layout = QVBoxLayout()

        # 创建搜索输入框
        self.search_input = QLineEdit()
        self.search_input.setPlaceholderText("输入搜索关键词")
        layout.addWidget(self.search_input)
        
        h_layout = QHBoxLayout()
        layout.addLayout(h_layout)
        
        # 创建搜索按钮
        self.search_button = QPushButton("搜索")
        self.search_button.clicked.connect(self.perform_search)
        h_layout.addWidget(self.search_button)

        self.close_button = QPushButton("关闭")
        self.close_button.clicked.connect(self.close)
        h_layout.addWidget(self.close_button)

        self.iscap_checkbox = QCheckBox("不区分大小写")
        layout.addWidget(self.iscap_checkbox)
        self.iscap_checkbox.setChecked(True)

        self.next_item_button = QPushButton("下一个")
        self.next_item_button.clicked.connect(self.next_item)
        h_layout.addWidget(self.next_item_button)
        
        # 设置布局
        self.setLayout(layout)
        
        # 设置窗口效果
        self.windowEffect = WindowEffect()
        self.setAttribute(Qt.WA_TranslucentBackground)
        self.setAttribute(Qt.WA_NoSystemBackground)
        self.move(500,500)
    
    def update_ui_theme(self):
        # 从父窗口获取主题设置
        if self.parent_player:
            is_dark = self.parent_player.is_dark
            bg_color = self.parent_player.bg_color
            text_color = self.parent_player.text_color
            effect = self.parent_player.effect
        else:
            # 默认主题
            is_dark = False
            bg_color = "rgba(255, 255, 255, 100)"
            text_color = "rgba(0, 0, 0, 230)"
        
        # 设置亚克力效果
        if is_dark:
            self.windowEffect.setAcrylicEffect(int(self.winId()), gradientColor="404040A0")
        else:
            if effect=="Acrylic":
                self.windowEffect.setAcrylicEffect(int(self.winId()), gradientColor="FFFFFF90")
            elif effect=="Aero":
                self.windowEffect.setAeroEffect(int(self.winId()))
            else:
                pass
        
        # 设置按钮样式
        button_style = f"""
            QPushButton {{
                background-color: {bg_color};
                color: {text_color};
                border: none;
                border-radius: 3px;
                padding: 5px;
                font-family: "Microsoft YaHei", "微软雅黑";
                font-size: 12px;
            }}
            QPushButton:hover {{
                background-color: rgba(120, 120, 120, 150);
            }}
        """
        self.search_button.setStyleSheet(button_style)
        self.close_button.setStyleSheet(button_style)
        self.next_item_button.setStyleSheet(button_style)
        
        # 设置复选框样式
        self.iscap_checkbox.setStyleSheet(f"""
            QCheckBox {{
                color: {text_color};
                font-family: "Microsoft YaHei", "微软雅黑";
                font-size: 12px;
            }}
        """)
        
        # 设置输入框样式
        self.search_input.setStyleSheet(f"""
            QLineEdit {{
                background-color: {bg_color};
                color: {text_color};
                border: none;
                border-radius: 3px;
                padding: 5px;
                font-family: "Microsoft YaHei", "微软雅黑";
                font-size: 12px;
            }}
        """)
    
    def perform_search(self):
        keyword = self.search_input.text()
        iscap = self.iscap_checkbox.isChecked()
        
        if keyword and self.parent_player:
            print(f"搜索关键词: {keyword}")
            self.parent_player.search_exec_runner(keyword, iscap)

    def closeEvent(self, event):
        # 清除搜索高亮
        if self.parent_player:
            self.parent_player.clear_highlight()
            self.parent_player.search_window = None  # 关键：关闭时清理引用
        
        event.accept()

    def next_item(self):
        if self.parent_player:
            self.parent_player.next_item()
if __name__ == "__main__":
    # 确保中文显示正常
    import matplotlib
    matplotlib.rcParams["font.family"] = ["consolas","SimHei", "WenQuanYi Micro Hei", "Heiti TC"]
    
    app = QApplication(sys.argv)
    player = MusicPlayer()
    sys.exit(app.exec_())