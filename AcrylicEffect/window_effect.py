# coding:utf-8

from ctypes import POINTER, c_bool, sizeof, addressof,windll,pointer,c_int,c_uint,byref,c_size_t,Structure,c_void_p
from ctypes.wintypes import DWORD, HWND, ULONG

from PyQt5.QtWinExtras import QtWin

from win32 import win32api, win32gui
from win32.lib import win32con

from .c_structures import (ACCENT_POLICY, ACCENT_STATE,
                           WINDOWCOMPOSITIONATTRIB,
                           WINDOWCOMPOSITIONATTRIBDATA)


class WindowEffect():
    """ 调用windows api实现窗口效果 """

    def __init__(self):
        # 调用api
        self.SetWindowCompositionAttribute = windll.user32.SetWindowCompositionAttribute
        self.SetWindowCompositionAttribute.restype = c_bool
        self.SetWindowCompositionAttribute.argtypes = [
            c_int, POINTER(WINDOWCOMPOSITIONATTRIBDATA)]
        # 初始化结构体
        self.accentPolicy = ACCENT_POLICY()
        self.winCompAttrData = WINDOWCOMPOSITIONATTRIBDATA()
        self.winCompAttrData.Attribute = WINDOWCOMPOSITIONATTRIB.WCA_ACCENT_POLICY.value[0]
        self.winCompAttrData.SizeOfData = sizeof(self.accentPolicy)
        self.winCompAttrData.Data = pointer(self.accentPolicy)

    def setAcrylicEffect(self, hWnd: int, gradientColor: str = 'F2F2F230', isEnableShadow: bool = True, animationId: int = 0):
        # 亚克力混合色
        gradientColor = gradientColor[6:] + gradientColor[4:6] + \
            gradientColor[2:4] + gradientColor[:2]
        gradientColor = DWORD(int(gradientColor, base=16))
        # 磨砂动画
        animationId = DWORD(animationId)
        # 窗口阴影
        accentFlags = DWORD(0x20 | 0x40 | 0x80 |
                            0x100) if isEnableShadow else DWORD(0)
        self.accentPolicy.AccentState = ACCENT_STATE.ACCENT_ENABLE_ACRYLICBLURBEHIND.value[0]
        self.accentPolicy.GradientColor = gradientColor
        self.accentPolicy.AccentFlags = accentFlags
        self.accentPolicy.AnimationId = animationId 
        # 开启亚克力
        self.SetWindowCompositionAttribute(hWnd, pointer(self.winCompAttrData))


    def setAeroEffect(self, hWnd: int):
        self.accentPolicy.AccentState = ACCENT_STATE.ACCENT_ENABLE_BLURBEHIND.value[0]
        # 开启Aero
        self.SetWindowCompositionAttribute(hWnd, pointer(self.winCompAttrData))
    def setMicaEffect(self, hWnd: int):
        self.accentPolicy.AccentState = ACCENT_STATE.ACCENT_ENABLE_MICA.value[0]
        # 开启Mica
        self.SetWindowCompositionAttribute(hWnd, pointer(self.winCompAttrData))
    def enable_mica_for_hwnd(hwnd, enable=True):
        """尝试为 hwnd 启用 Mica（Windows 11）；返回 True/False 表示是否成功或已应用回退方案。"""
        # 尝试 DwmSetWindowAttribute -> DWMWA_SYSTEMBACKDROP_TYPE (Windows 11)
        try:
            user32 = windll.user32
            dwmapi = windll.dwmapi
        except Exception:
            return False

        # 常量：如果你使用 Visual Studio SDK，DWMWA_SYSTEMBACKDROP_TYPE = 38
        # SystemBackdropType: 0 = auto, 1 = none, 2 = mainwindow, 3 = transient
        try:
            DWMWA_SYSTEMBACKDROP_TYPE = 38  # 仅在新版Windows SDK里定义；如无效会抛错或无效果
            # 选择 2（DWMSBT_MAINWINDOW）通常用于主窗口的 Mica
            value = c_int(2 if enable else 1)
            res = dwmapi.DwmSetWindowAttribute(HWND(hwnd),
                                            c_uint(DWMWA_SYSTEMBACKDROP_TYPE),
                                            byref(value),
                                            sizeof(value))
            return res == 0
        except Exception:
            # 回退到 SetWindowCompositionAttribute + AccentPolicy
            pass

        # 回退：SetWindowCompositionAttribute + ACCENT_POLICY (third-party 常用做回退)
        try:
            class ACCENT_POLICY(Structure):
                _fields_ = [("AccentState", c_int),
                            ("AccentFlags", c_int),
                            ("GradientColor", c_uint),
                            ("AnimationId", c_int)]

            class WINDOWCOMPOSITIONATTRIBDATA(Structure):
                _fields_ = [("Attribute", c_int),
                            ("Data", c_void_p),
                            ("SizeOfData", c_size_t)]

            # 从 repo 的 c_structures.py 可引用 ACCENT_ENABLE_MICA = 6
            ACCENT_ENABLE_MICA = 6
            Accent = ACCENT_POLICY()
            Accent.AccentState = ACCENT_ENABLE_MICA if enable else 0
            Accent.AccentFlags = 0
            Accent.GradientColor = 0
            Accent.AnimationId = 0

            data = WINDOWCOMPOSITIONATTRIBDATA()
            WCA_ACCENT_POLICY = 19  # WCA_ACCENT_POLICY 常用值
            data.Attribute = WCA_ACCENT_POLICY
            data.SizeOfData = sizeof(Accent)
            data.Data = addressof(Accent)

            set_window_comp_attr = user32.SetWindowCompositionAttribute
            set_window_comp_attr.restype = c_bool
            set_window_comp_attr.argtypes = (HWND, POINTER(WINDOWCOMPOSITIONATTRIBDATA))

            res = set_window_comp_attr(HWND(hwnd), byref(data))
            return bool(res)
        except Exception:
            return False
    def setShadowEffect(self, widget, isEnableShadow: bool):
        if not isEnableShadow:
            class_style = win32gui.GetClassLong(hWnd, win32con.GCL_STYLE)
            class_style = class_style & (~0x00020000)
            win32api.SetClassLong(widget.winId(), GCL_STYLE, class_style)
            return
        QtWin.extendFrameIntoClientArea(widget, -1, -1, -1, -1)
        
    def moveWindow(self, hWnd: int):
        win32gui.ReleaseCapture()
        win32api.SendMessage(hWnd, win32con.WM_SYSCOMMAND,
                    win32con.SC_MOVE + win32con.HTCAPTION, 0)

        
