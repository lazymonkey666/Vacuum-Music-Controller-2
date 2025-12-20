import ctypes
from ctypes import wintypes, POINTER, c_bool, sizeof, addressof, windll, pointer, c_int, c_uint, byref, c_size_t, Structure, c_void_p, cast

from PyQt5.QtWinExtras import QtWin
from win32 import win32api, win32gui
from win32.lib import win32con

# -------------------------- DWM相关API和结构体 --------------------------
dwmapi = windll.dwmapi

# 从wintypes导入类型
DWORD = wintypes.DWORD
HWND = wintypes.HWND
ULONG = wintypes.ULONG

class MARGINS(Structure):
    _fields_ = [
        ("cxLeftWidth", wintypes.LONG),
        ("cxRightWidth", wintypes.LONG),
        ("cyTopHeight", wintypes.LONG),
        ("cyBottomHeight", wintypes.LONG)
    ]

DwmIsCompositionEnabled = dwmapi.DwmIsCompositionEnabled
DwmIsCompositionEnabled.restype = ctypes.HRESULT  
DwmIsCompositionEnabled.argtypes = [POINTER(wintypes.BOOL)]

DwmExtendFrameIntoClientArea = dwmapi.DwmExtendFrameIntoClientArea
DwmExtendFrameIntoClientArea.restype = ctypes.HRESULT
DwmExtendFrameIntoClientArea.argtypes = [wintypes.HWND, POINTER(MARGINS)]

# -------------------------- Windows Composition API结构体 --------------------------
class ACCENT_POLICY(Structure):
    _fields_ = [
        ("AccentState", c_int),
        ("AccentFlags", c_int),
        ("GradientColor", c_uint),
        ("AnimationId", c_int)
    ]

class WINDOWCOMPOSITIONATTRIBDATA(Structure):
    _fields_ = [
        ("Attribute", c_int),
        ("Data", c_void_p),
        ("SizeOfData", c_size_t)
    ]
DWMWA_SYSTEMBACKDROP_TYPE = 38
DWMSBT_MAINWINDOW = 2  # Mica（带主题色）
DWMSBT_TABBED_WINDOW = 4  # Mica Alt（无主题色）
# 枚举定义
class ACCENT_STATE:
    ACCENT_DISABLED = 0
    ACCENT_ENABLE_GRADIENT = 1
    ACCENT_ENABLE_TRANSPARENTGRADIENT = 2
    ACCENT_ENABLE_BLURBEHIND = 3
    ACCENT_ENABLE_ACRYLICBLURBEHIND = 4
    ACCENT_ENABLE_HOSTBACKDROP = 5
    ACCENT_INVALID_STATE = 6

class WINDOWCOMPOSITIONATTRIB:
    WCA_ACCENT_POLICY = 19


class WindowEffect():
    """ 调用windows api实现窗口效果 """

    def __init__(self):
        # 初始化SetWindowCompositionAttribute
        self.SetWindowCompositionAttribute = windll.user32.SetWindowCompositionAttribute
        self.SetWindowCompositionAttribute.restype = c_bool
        self.SetWindowCompositionAttribute.argtypes = [
            c_int, POINTER(WINDOWCOMPOSITIONATTRIBDATA)]
        
        # 初始化结构体
        self.accentPolicy = ACCENT_POLICY()
        self.winCompAttrData = WINDOWCOMPOSITIONATTRIBDATA()
        self.winCompAttrData.Attribute = WINDOWCOMPOSITIONATTRIB.WCA_ACCENT_POLICY
        self.winCompAttrData.SizeOfData = sizeof(self.accentPolicy)
        # 使用cast将指针转换为c_void_p类型
        self.winCompAttrData.Data = cast(pointer(self.accentPolicy), c_void_p)

    def setAcrylicEffect(self, hWnd: int, gradientColor: str = 'F2F2F230', isEnableShadow: bool = True, animationId: int = 0):
        """设置亚克力效果"""
        gradientColor = gradientColor[6:] + gradientColor[4:6] + \
            gradientColor[2:4] + gradientColor[:2]
        # 转换为正确的类型
        gradientColor = c_uint(int(gradientColor, base=16))
        animationId = c_int(animationId)
        accentFlags = c_int(0x20 | 0x40 | 0x80 |
                            0x100) if isEnableShadow else c_int(0)
        
        self.accentPolicy.AccentState = ACCENT_STATE.ACCENT_ENABLE_ACRYLICBLURBEHIND
        self.accentPolicy.GradientColor = gradientColor.value  # 使用.value获取整数值
        self.accentPolicy.AccentFlags = accentFlags.value
        self.accentPolicy.AnimationId = animationId.value
        self.SetWindowCompositionAttribute(hWnd, pointer(self.winCompAttrData))

    def setAeroEffect(self, hWnd: int):
        """设置Windows 7 Aero Glass效果"""
        # 设置MARGINS：将整个客户区都扩展为玻璃区域
        margins = MARGINS(-1, -1, -1, -1)
        hwnd_ = wintypes.HWND(int(hWnd))
        DwmExtendFrameIntoClientArea(hwnd_, byref(margins))

    def checkAeroEnabled(self) -> bool:
        """检查系统是否启用Aero效果"""
        is_composition_enabled = wintypes.BOOL()
        hr = DwmIsCompositionEnabled(byref(is_composition_enabled))
        return hr == 0 and is_composition_enabled

    def setMicaEffect(self, hwnd: int,use_alt: bool = False):
        dwmapi = ctypes.WinDLL("dwmapi", use_last_error=True)
        dwmapi.DwmSetWindowAttribute.restype = c_int
        dwmapi.DwmSetWindowAttribute.argtypes = [HWND, c_uint, c_void_p, c_uint]
        backdrop_type = c_int(DWMSBT_TABBED_WINDOW if use_alt else DWMSBT_MAINWINDOW)
        result = dwmapi.DwmSetWindowAttribute(
            HWND(hwnd),
            c_uint(DWMWA_SYSTEMBACKDROP_TYPE),
            byref(backdrop_type),
            c_uint(sizeof(backdrop_type))
        )

    def setShadowEffect(self, widget, isEnableShadow: bool):
        """设置窗口阴影效果"""
        hWnd = widget.winId()
        if not isEnableShadow:
            class_style = win32gui.GetClassLong(hWnd, win32con.GCL_STYLE)
            class_style = class_style & (~0x00020000)
            win32api.SetClassLong(hWnd, win32con.GCL_STYLE, class_style)
            return
        QtWin.extendFrameIntoClientArea(widget, -1, -1, -1, -1)
        
    def moveWindow(self, hWnd: int):
        """移动窗口（用于无边框窗口拖拽）"""
        win32gui.ReleaseCapture()
        win32api.SendMessage(hWnd, win32con.WM_SYSCOMMAND,
                    win32con.SC_MOVE + win32con.HTCAPTION, 0)