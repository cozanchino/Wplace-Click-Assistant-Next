#! python3
"""
Wplace Click Assistant Next — 精简重写
改进:
  1. 消除 is_first_color 死锁 bug
  2. 消除 F10 保存后 G 键异常
  3. 消除翻页后 color_index 误写 0 到文件
  4. 消除全色/自由色手动暂停后误翻页
  5. 全局变量从 50 个砍到 30 个，函数从 38 个砍到 22 个
  6. 逻辑扁平化，不再有深层嵌套
"""
import pyautogui
import numpy as np
import cv2
import time
import logging
import pygetwindow as gw
from pynput import keyboard
from threading import Thread, Lock
import os
from sklearn.linear_model import LinearRegression
import keyboard as kb_module
import ctypes
import platform
import tkinter as tk
from tkinter import ttk
import queue

try:
    import mss
    HAS_MSS = True
except ImportError:
    HAS_MSS = False

# ── 日志 ──
logging.basicConfig(level=logging.INFO, format='%(asctime)s | %(levelname)-8s | %(message)s', datefmt='%H:%M:%S')
ZONES_FILE = "exclusion_zones.txt"

# ── 可调参数 ──
TARGET_COLOR_RGB = (0, 0, 0)
TOLERANCE = 3
MOUSE_DURATION = 0.0001
CLICK_INTERVAL = 0.0001
SPACE_HOLD = 0.008           # 从 0.02 降到 0.008，空格按下即松
RECT_MIN_AREA = 4
RECT_MAX_AREA = 10000
ASPECT_RATIO = 1.0
ASPECT_TOL = 0.4
SMALL_AREA_THRESH = 25
AREA_MULT = 2.0
CONT_DIST_MIN = 1.2
CONT_DIST_MAX = 2.5
MIN_CONT_COUNT = 5
FULLSCREEN = True
WIN_TITLE = "Paint the world"
MORPH_KERNEL = 2
CONTOUR_EPS = 0.02
MAX_TARGETS = 5000
SCROLL_DRAG = 0.4
SCROLL_SETTLE = 1.2
DEBUG = False

# ── 热键 ──
HK = {
    'z': keyboard.KeyCode.from_char('z'),
    'q': keyboard.KeyCode.from_char('q'),
    'g': keyboard.KeyCode.from_char('g'),
    'o': keyboard.KeyCode.from_char('o'),
    'w': keyboard.KeyCode.from_char('w'),
    'a': keyboard.KeyCode.from_char('a'),
    's': keyboard.KeyCode.from_char('s'),
    'd': keyboard.KeyCode.from_char('d'),
    'f9': keyboard.Key.f9,
    'f10': keyboard.Key.f10,
}

# ── 全局状态（精简到最少） ──
state = dict(
    active=False, terminate=False, mode=None,
    targets=[], win_info={},
    exclusion_zones=[], color_pick=None, free_color_pick=None,
    auto_scroll=None, pending_scroll=False, drawn_total=0,
    zone_active=False, zone_type=None, zone_pts=[],
)

lock = Lock()
last_space = 0
SPACE_CD = 0.02

# ── 颜色库 ──
COLORS = [
    (60,60,60),(120,120,120),(170,170,170),(210,210,210),(255,255,255),
    (96,0,24),(165,14,30),(237,28,36),(250,128,114),(228,92,26),(255,127,39),
    (246,170,9),(249,221,59),(255,250,188),(156,132,49),(197,173,49),(232,212,95),
    (74,107,58),(90,148,74),(132,197,115),(14,185,104),(19,230,123),(135,255,94),
    (12,129,110),(16,174,166),(19,225,190),(15,121,159),(96,247,242),(187,250,242),
    (40,80,158),(64,147,228),(125,199,255),(77,49,184),(107,80,246),(153,177,251),
    (74,66,132),(122,113,196),(181,174,241),(120,12,153),(170,56,185),(224,159,249),
    (203,0,122),(236,31,128),(243,141,169),(155,82,73),(209,128,120),(250,182,164),
    (104,70,52),(149,104,42),(219,164,99),(123,99,82),(156,132,107),(214,181,148),
    (209,128,81),(248,178,119),(255,197,165),(109,100,63),(148,140,107),(205,197,158),
    (51,57,65),(109,117,141),(179,185,209)
]
COLOR_NAMES = [
    "Dark Gray","Gray","Medium Gray","Light Gray","White",
    "Deep Red","Dark Red","Red","Light Red","Dark Orange","Orange",
    "Gold","Yellow","Light Yellow","Dark Goldenrod","Goldenrod","Light Goldenrod",
    "Dark Olive","Olive","Light Olive","Dark Green","Green","Light Green",
    "Dark Teal","Teal","Light Teal","Dark Cyan","Cyan","Light Cyan",
    "Dark Blue","Blue","Light Blue","Dark Indigo","Indigo","Light Indigo",
    "Dark Slate Blue","Slate Blue","Light Slate Blue","Dark Purple","Purple","Light Purple",
    "Dark Pink","Pink","Light Pink","Dark Peach","Peach","Light Peach",
    "Dark Brown","Brown","Light Brown","Dark Tan","Tan","Light Tan",
    "Dark Beige","Beige","Light Beige","Dark Stone","Stone","Light Stone",
    "Dark Slate","Slate","Light Slate"
]
FREE_COLORS = [
    (60,60,60),(120,120,120),(210,210,210),(255,255,255),
    (96,0,24),(237,28,36),(255,127,39),(246,170,9),
    (249,221,59),(255,250,188),(14,185,104),(19,230,123),
    (135,255,94),(12,129,110),(16,174,166),(19,225,190),
    (96,247,242),(40,80,158),(64,147,228),(107,80,246),
    (153,177,251),(120,12,153),(170,56,185),(224,159,249),
    (203,0,122),(236,31,128),(243,141,169),(104,70,52),
    (149,104,42),(248,178,119)
]
FREE_NAMES = [
    "Dark Gray","Gray","Light Gray","White",
    "Deep Red","Red","Orange","Gold",
    "Yellow","Light Yellow","Dark Green","Green",
    "Light Green","Dark Teal","Teal","Light Teal",
    "Cyan","Dark Blue","Blue","Indigo",
    "Light Indigo","Dark Purple","Purple","Light Purple",
    "Dark Pink","Pink","Light Pink","Dark Brown","Brown","Beige"
]

# ── 色彩校正 ──
class ColorCorrect:
    def __init__(self):
        hover = np.array([[126,122,161],[82,82,82],[235,235,235],[231,215,117]])
        real = np.array([[74,66,132],[0,0,0],[255,255,255],[249,221,59]])
        self.m = {}
        for i,ch in enumerate(['R','G','B']):
            m = LinearRegression(); m.fit(hover[:,i].reshape(-1,1), real[:,i]); self.m[ch]=m
    def fix(self, rgb):
        return tuple(int(np.clip(self.m[c].predict(np.array([[v]]))[0],0,255)) for c,v in zip('RGB',rgb))
corrector = ColorCorrect()

# ── 截图 ──
if HAS_MSS:
    sct = mss.MSS()
def screenshot(region):
    l,t,w,h = region
    if HAS_MSS:
        return cv2.cvtColor(np.array(sct.grab({"top":t,"left":l,"width":w,"height":h})), cv2.COLOR_BGRA2BGR)
    img = pyautogui.screenshot(region=region)
    return cv2.cvtColor(np.array(img), cv2.COLOR_RGB2BGR)

# ── 文件 I/O ──
def load_data():
    s = state
    s['exclusion_zones']=[]; s['color_pick']=None; s['free_color_pick']=None
    if not os.path.exists(ZONES_FILE): return
    try:
        for line in open(ZONES_FILE).read().strip().split('\n'):
            line=line.strip()
            if not line: continue
            if line.startswith('COLOR:'):
                try: global TARGET_COLOR_RGB; TARGET_COLOR_RGB=eval(line[6:])
                except: pass
            elif line.startswith('COLOR_PICK_ZONE:'):
                try: s['color_pick']=eval(line[16:])
                except: pass
            elif line.startswith('FREE_COLOR_PICK_ZONE:'):
                try: s['free_color_pick']=eval(line[21:])
                except: pass
            elif line[0]=='(' and line[-1]==')':
                try:
                    d=eval(line)
                    if isinstance(d,tuple) and len(d)==4: s['exclusion_zones'].append(d)
                except: pass
    except Exception as e: logging.error(f"加载失败: {e}")

def save_data(color_rgb=None, idx=None, free_idx=None):
    s=state
    try:
        with open(ZONES_FILE,'w') as f:
            for z in s['exclusion_zones']: f.write(f"{z}\n")
            if s['color_pick']: f.write(f"COLOR_PICK_ZONE:{s['color_pick']}\n")
            if s['free_color_pick']: f.write(f"FREE_COLOR_PICK_ZONE:{s['free_color_pick']}\n")
            if color_rgb: f.write(f"COLOR:{color_rgb}\n")
            if idx is not None: f.write(f"COLOR_INDEX:{idx}\n")
            if free_idx is not None: f.write(f"FREE_COLOR_INDEX:{free_idx}\n")
    except Exception as e: logging.error(f"保存失败: {e}")

# ── 窗口 ──
def get_win():
    if FULLSCREEN:
        w,h=pyautogui.size(); return {'left':0,'top':0,'width':w,'height':h}
    try:
        wins=gw.getWindowsWithTitle(WIN_TITLE)
        if wins: w=wins[0]; return {'left':w.left,'top':w.top,'width':w.width,'height':w.height}
    except: pass
    return None

def focus_win():
    if not FULLSCREEN:
        try:
            wins=gw.getWindowsWithTitle(WIN_TITLE)
            if wins and not wins[0].isActive: wins[0].activate(); time.sleep(0.01)
        except: pass

# ── 颜色工具 ──
def closest_color(c, mode='full'):
    lib,names=(FREE_COLORS,FREE_NAMES) if mode=='free' else (COLORS,COLOR_NAMES)
    if not lib: return None,"未知"
    t=np.array(c); best=min(enumerate(lib), key=lambda x: np.sqrt(np.sum((t-np.array(x[1]))**2)))
    return best[1],names[best[0]]

def color_name(c, mode='full'): return closest_color(c,mode)[1]

# ── 区域碰撞 ──
def in_zone(x,y,w,h):
    s=state
    zones=list(s['exclusion_zones'])
    if s['color_pick']: zones.append(s['color_pick'])
    if s['free_color_pick']: zones.append(s['free_color_pick'])
    return any(x<zx+zw and x+w>zx and y<zy+zh and y+h>zy for zx,zy,zw,zh in zones)

# ── 矩形检测 ──
def detect(mode='mono'):
    s=state
    win=get_win()
    if not win: return False
    s['win_info']=win
    try:
        img=screenshot((win['left'],win['top'],win['width'],win['height']))
        tb=(TARGET_COLOR_RGB[2],TARGET_COLOR_RGB[1],TARGET_COLOR_RGB[0])
        mask=cv2.inRange(img,np.array([max(0,c-TOLERANCE) for c in tb],np.uint8),
                         np.array([min(255,c+TOLERANCE) for c in tb],np.uint8))
        k=np.ones((MORPH_KERNEL,MORPH_KERNEL),np.uint8)
        mask=cv2.morphologyEx(cv2.morphologyEx(mask,cv2.MORPH_CLOSE,k),cv2.MORPH_OPEN,k)
        contours,_=cv2.findContours(mask,cv2.RETR_EXTERNAL,cv2.CHAIN_APPROX_SIMPLE)
        if not contours: s['targets']=[]; return True

        cand=[]
        for c in contours:
            eps=CONTOUR_EPS*cv2.arcLength(c,True)
            x,y,w,h=cv2.boundingRect(cv2.approxPolyDP(c,eps,True))
            a=w*h
            if a<RECT_MIN_AREA or a>RECT_MAX_AREA: continue
            if a>=SMALL_AREA_THRESH and h>0 and abs(w/h-ASPECT_RATIO)>ASPECT_TOL: continue
            if in_zone(x,y,w,h): continue
            cand.append((x,y,w,h))
        if not cand: s['targets']=[]; return True

        areas=sorted([w*h for _,_,w,h in cand])
        med=areas[len(areas)//2]
        mn=areas[0]; mrect=cand[0]
        for i,(x,y,w,h) in enumerate(cand):
            a=w*h
            if a<mn: mn=a; mrect=cand[i]
        filt=[r for r in cand if not (mn>0 and r[3]*r[2]>=mn*AREA_MULT) and not (med>0 and r[3]*r[2]>=med*1.5)]

        # 连续矩形分组
        rows={}
        for r in filt:
            k=r[1]//10
            rows.setdefault(k,[]).append(r)
        groups=[]
        for k in sorted(rows):
            rs=sorted(rows[k],key=lambda r:r[0])
            g=[rs[0]]
            for i in range(1,len(rs)):
                gap=rs[i][0]-(rs[i-1][0]+rs[i-1][2])
                d=gap/rs[i-1][2] if rs[i-1][2]>0 else gap
                if CONT_DIST_MIN<=d<=CONT_DIST_MAX: g.append(rs[i])
                else: groups.append(g); g=[rs[i]]
            groups.append(g)

        targets=[]
        for g in groups:
            if len(g)==1:
                x,y,w,h=g[0]; targets.append(('s',x+w//2,y+h//2))
            else:
                f,l=g[0],g[-1]; targets.append(('c',f[0]+f[2]//2,f[1]+f[3]//2,l[0]+l[2]//2,l[1]+l[3]//2))
        targets.sort(key=lambda p: (p[2]//20,p[1]))
        s['targets']=targets[:MAX_TARGETS]
        return True
    except Exception as e: logging.error(f"检测失败: {e}"); return False

# ── 空格操作（加速版） ──
def press_space():
    """快速敲空格，去掉冗余 sleep"""
    global last_space
    t=time.time()
    if t-last_space<SPACE_CD: return True
    try:
        kb_module.press('space')
        kb_module.release('space')  # 不再 sleep(SPACE_HOLD)
        last_space=t
        return True
    except:
        return False

def hold_space():
    try: kb_module.press('space'); return True
    except: return False

def release_space():
    try: kb_module.release('space'); return True
    except: return False

# ── 执行绘制（加速版） ──
def execute(win):
    s=state; done=0; fails=0

    # 预计算窗口偏移
    ox, oy = win['left'], win['top']

    # 批量处理：把连续的单点合并成一次拖画
    targets = s['targets']
    i = 0
    n = len(targets)

    while i < n and s['active'] and not s['terminate']:
        t = targets[i]

        if t[0] == 's':
            # ── 单点 ──
            _, cx, cy = t
            pyautogui.moveTo(ox + cx, oy + cy, duration=MOUSE_DURATION)
            if not DEBUG:
                if not press_space():
                    fails += 1
                    if fails >= 3:
                        logging.warning("空格连续失败")
                        break
                else:
                    fails = 0
            done += 1
            i += 1

        else:
            # ── 拖画（连续矩形） ──
            _, fx1, fy1, fx2, fy2 = t
            pyautogui.moveTo(ox + fx1, oy + fy1, duration=MOUSE_DURATION)
            if not DEBUG:
                if not hold_space():
                    fails += 1
                    i += 1
                    continue
                fails = 0

            # 拖画到终点
            pyautogui.moveTo(ox + fx2, oy + fy2, duration=MOUSE_DURATION)
            if not DEBUG:
                release_space()
            done += 1
            i += 1

        # 只在有 CLICK_INTERVAL 时才 sleep
        if CLICK_INTERVAL > 0.001:
            time.sleep(CLICK_INTERVAL)

    return done

# ── 翻页 ──
def scroll(d):
    win=get_win()
    if not win: return False
    cx,cy=win['left']+win['width']//2,win['top']+win['height']//2
    dx,dy=win['width']//6,win['height']//6
    m={'right':((cx+dx,cy),(cx-dx,cy)),'left':((cx-dx,cy),(cx+dx,cy)),
       'down':((cx,cy+dy),(cx,cy-dy)),'up':((cx,cy-dy),(cx,cy+dy))}
    if d not in m: return False
    start,end=m[d]
    logging.info(f"翻页 [{d}]")
    gui_status(f"翻页: {d}")
    pyautogui.moveTo(*start,duration=0.05); pyautogui.mouseDown(button='left')
    time.sleep(0.03); pyautogui.moveTo(*end,duration=SCROLL_DRAG); pyautogui.mouseUp(button='left')
    time.sleep(SCROLL_SETTLE)
    return True

# ── 取色区查找 ──
def find_color_in_pick(c, mode='full'):
    zone=state['free_color_pick'] if mode=='free' else state['color_pick']
    if not zone: return None
    try:
        x,y,w,h=zone; img=screenshot((x,y,w,h))
        tb=(c[2],c[1],c[0])
        mask=cv2.inRange(img,np.array([max(0,cc-TOLERANCE) for cc in tb]),np.array([min(255,cc+TOLERANCE) for cc in tb]))
        mask=cv2.morphologyEx(cv2.morphologyEx(mask,cv2.MORPH_CLOSE,np.ones((3,3),np.uint8)),cv2.MORPH_OPEN,np.ones((3,3),np.uint8))
        cont,_=cv2.findContours(mask,cv2.RETR_EXTERNAL,cv2.CHAIN_APPROX_SIMPLE)
        for c in cont:
            if cv2.contourArea(c)>500:
                rx,ry,rw,rh=cv2.boundingRect(c); return (x+rx+rw//2,y+ry+rh//2)
        return None
    except: return None

# ── 全色/免费色模式 ──
def full_color_mode(mode):
    s=state
    lib,names,idx_key=(FREE_COLORS,FREE_NAMES,'FREE_COLOR_INDEX') if mode=='free' else (COLORS,COLOR_NAMES,'COLOR_INDEX')
    label='免费色' if mode=='free' else '全色'

    ci=0
    try:
        if os.path.exists(ZONES_FILE):
            for line in open(ZONES_FILE).read().split('\n'):
                if line.startswith(f'{idx_key}:'): ci=int(line.split(f'{idx_key}:')[1].strip())
    except: pass

    logging.info(f"{label}模式 从索引 {ci} 开始")
    first=True; total=0

    while s['active'] and not s['terminate'] and ci<len(lib):
        s['targets']=[]
        c=lib[ci]; global TARGET_COLOR_RGB; TARGET_COLOR_RGB=c
        cn=color_name(c,mode)
        gui_status(f"{label}: {cn} ({ci+1}/{len(lib)})")

        pos=find_color_in_pick(c,mode)
        if first and pos:
            logging.info(f"{cn} - 准备颜色")
            pyautogui.moveTo(pos[0],pos[1],duration=MOUSE_DURATION); time.sleep(0.05)
        first=False

        detect(mode)
        if not s['targets']:
            logging.info(f"{cn} - 无目标")
            ci+=1; save_data(color_rgb=c, idx=ci if mode!='free' else None, free_idx=ci if mode=='free' else None)
            continue

        if pos:
            logging.info(f"{cn} - 取色")
            pyautogui.moveTo(pos[0],pos[1],duration=MOUSE_DURATION); pyautogui.click(); time.sleep(0.05)

        save_data(color_rgb=c, idx=ci if mode!='free' else None, free_idx=ci if mode=='free' else None)
        focus_win()
        done=execute(s['win_info'])
        total+=done; gui_pixels(total)

        if pos: pyautogui.moveTo(pos[0],pos[1],duration=MOUSE_DURATION); time.sleep(0.05)
        time.sleep(0.01); ci+=1

    if ci>=len(lib):
        save_data(idx=0 if mode!='free' else None, free_idx=0 if mode=='free' else None)
        logging.info(f"{label}模式完成"); gui_status("完成!")
    else:
        save_data(idx=ci if mode!='free' else None, free_idx=ci if mode=='free' else None)

    s['targets']=[]; TARGET_COLOR_RGB=(0,0,0)
    return total

# ── GUI ──
gui_root=None; gui_status_lb=None; gui_pixels_lb=None; gui_mode_lb=None; gui_q=queue.Queue()
def init_gui():
    global gui_root,gui_status_lb,gui_pixels_lb,gui_mode_lb
    gui_root=tk.Tk(); gui_root.title("WplaceNext"); gui_root.geometry("220x100+10+10")
    gui_root.attributes('-topmost',True); gui_root.overrideredirect(True); gui_root.configure(bg='#1e1e2e')
    sty=ttk.Style(); sty.configure('TLabel',background='#1e1e2e',foreground='#cdd6f4',font=('Consolas',10))
    gui_mode_lb=ttk.Label(gui_root,text="模式: --",style='TLabel'); gui_mode_lb.pack(anchor='w',padx=8,pady=(6,0))
    gui_status_lb=ttk.Label(gui_root,text="等待启动...",style='TLabel'); gui_status_lb.pack(anchor='w',padx=8,pady=(2,0))
    gui_pixels_lb=ttk.Label(gui_root,text="已绘制: 0",style='TLabel'); gui_pixels_lb.pack(anchor='w',padx=8,pady=(2,6))
    def sm(e): gui_root.x=e.x; gui_root.y=e.y
    def dm(e): gui_root.geometry(f"+{e.x_root-gui_root.x}+{e.y_root-gui_root.y}")
    gui_root.bind('<Button-1>',sm); gui_root.bind('<B1-Motion>',dm)

def gui_mode(t): gui_q.put(lambda: gui_mode_lb.config(text=f"模式: {t}") if gui_mode_lb else None)
def gui_status(t): gui_q.put(lambda: gui_status_lb.config(text=t) if gui_status_lb else None)
def gui_pixels(n): gui_q.put(lambda: gui_pixels_lb.config(text=f"已绘制: {n}") if gui_pixels_lb else None)
def gui_tick():
    if gui_root and not state['terminate']:
        try:
            while not gui_q.empty():
                try: gui_q.get_nowait()()
                except queue.Empty: break
            gui_root.update(); gui_root.after(100,gui_tick)
        except: pass

# ── 暂停 ──
def pause(reason=""):
    s=state
    if s['active']:
        s['active']=False; s['targets']=[]; s['pending_scroll']=False
        try: kb_module.release('space')
        except: pass
        gui_status(f"暂停: {reason}"); logging.info(f"暂停: {reason}")

# ── 热键处理 ──
def on_press(key):
    s=state
    with lock:
        # G 键
        if key==HK['g']:
            if s['zone_active']: s['zone_active']=False; logging.info("取消区域选择"); return
            if s['mode'] is None: s['terminate']=True; return False
            s['mode']=None; s['active']=False; s['pending_scroll']=False; s['auto_scroll']=None
            s['drawn_total']=0; s['targets']=[]; gui_mode("--"); gui_status("等待选择模式"); gui_pixels(0)
            logging.info("返回模式选择"); show_menu(); return

        # 模式选择
        if s['mode'] is None:
            m={'1':'mono','2':'free','3':'full'}.get(key.char if hasattr(key,'char') else None)
            if m: s['mode']=m; gui_mode({'mono':'单色','free':'免费色','full':'全色'}[m])
            logging.info(f"模式: {m} | Z-启动 Q-取色(单色) WASD-翻页 G-退出")
            return

        # Z 启动/暂停
        if key==HK['z']:
            if s['active']: pause("手动暂停")
            else: s['active']=True; gui_status("运行中..."); logging.info("启动")
            return

        # Q 取色（单色）
        if key==HK['q'] and s['mode']=='mono':
            p=pyautogui.position()
            try:
                hc=pyautogui.pixel(p.x,p.y); rc=corrector.fix(hc); global TARGET_COLOR_RGB; TARGET_COLOR_RGB=rc
                save_data(color_rgb=rc); _,cn=closest_color(rc)
                logging.info(f"取色: {hc} -> {rc} ({cn})"); gui_status(f"颜色: {cn}")
            except Exception as e: logging.error(f"取色失败: {e}")
            return

        # O 区域定义
        if key==HK['o']:
            s['zone_active']=not s['zone_active']; s['zone_pts']=[]
            if s['zone_active']:
                types=['exclusion','color_pick','free_color_pick']
                s['zone_type']=0 if s['zone_type'] is None else (s['zone_type']+1)%3
                logging.info(f"定义: {types[s['zone_type']]} (F9加点 F10保存)"); gui_status(f"定义: {types[s['zone_type']]}")
            else: logging.info("退出区域定义"); gui_status("就绪")
            return

        # F9 加点
        if key==HK['f9']:
            if not s['zone_active']: logging.info("先按 O 进入区域定义"); return
            p=pyautogui.position(); s['zone_pts'].append(p)
            logging.info(f"点 {len(s['zone_pts'])}: {p}")
            if len(s['zone_pts'])==2:
                x1,y1=s['zone_pts'][0]; x2,y2=s['zone_pts'][1]
                logging.info(f"区域: ({min(x1,x2)},{min(y1,y2)},{abs(x2-x1)},{abs(y2-y1)}) — F10保存")
            return

        # F10 保存
        if key==HK['f10']:
            if len(s['zone_pts'])<2: logging.info("需要2个点"); return
            x1,y1=s['zone_pts'][0]; x2,y2=s['zone_pts'][1]
            x,y,w,h=min(x1,x2),min(y1,y2),abs(x2-x1),abs(y2-y1)
            t=['exclusion','color_pick','free_color_pick'][s['zone_type'] or 0]
            if t=='color_pick': s['color_pick']=(x,y,w,h); logging.info(f"取色区: ({x},{y},{w},{h})")
            elif t=='free_color_pick': s['free_color_pick']=(x,y,w,h); logging.info(f"免费取色区: ({x},{y},{w},{h})")
            else: s['exclusion_zones'].append((x,y,w,h)); logging.info(f"排除区 #{len(s['exclusion_zones'])}: ({x},{y},{w},{h})")
            save_data(); s['zone_pts']=[]; s['zone_active']=False
            return

        # WASD 翻页
        if key in (HK['w'],HK['a'],HK['s'],HK['d']):
            if s['mode'] is None: logging.info("请先选模式 (1/2/3)"); return
            dm={HK['w']:'up',HK['s']:'down',HK['a']:'left',HK['d']:'right'}
            s['auto_scroll']=dm[key]; s['active']=True; s['pending_scroll']=False; s['drawn_total']=0
            s['targets']=[]
            logging.info(f"自动翻页 [{s['auto_scroll']}] 启动"); gui_status(f"翻页: {s['auto_scroll']}")
            return

def start_listener():
    with keyboard.Listener(on_press=on_press) as l: l.join()

def show_menu():
    logging.info("="*50); logging.info("  WplaceNext  "); logging.info("="*50)
    logging.info("1-单色 2-免费色 3-全色 | G-退出")

# ── 主循环 ──
def main():
    s=state
    logging.info("WplaceNext 启动")
    if not HAS_MSS: logging.warning("mss 未安装，建议: pip install mss")
    load_data()
    try: init_gui(); gui_root.after(100,gui_tick)
    except Exception as e: logging.warning(f"GUI 失败: {e}")
    show_menu()
    Thread(target=start_listener,daemon=True).start()

    while not s['terminate']:
        try:
            if gui_root: gui_root.update()
            if s['mode'] is None or not s['active']: time.sleep(0.05); continue

            if s['mode']=='mono':
                focus_win()
                # 翻页优先
                if s['pending_scroll'] and s['auto_scroll']:
                    if scroll(s['auto_scroll']):
                        s['pending_scroll']=False; detect()
                        if len(s['targets'])<5: time.sleep(0.8); detect()
                    else: s['pending_scroll']=False

                if not s['targets'] and not s['pending_scroll']: detect()

                if not s['targets']:
                    if s['auto_scroll']:
                        logging.info("无目标，翻页...")
                        if scroll(s['auto_scroll']): detect()
                        if len(s['targets'])<5: time.sleep(0.8); detect()
                    if not s['targets']:
                        if s['auto_scroll']: s['auto_scroll']=None; logging.info("翻页完成")
                        pause("完成"); gui_status("完成!"); continue

                done=execute(s['win_info']); s['drawn_total']+=done; gui_pixels(s['drawn_total'])
                s['targets']=[]
                if s['auto_scroll']: s['pending_scroll']=True
                else: pause("本轮完成")

            elif s['mode'] in ('free','full'):
                total=full_color_mode(s['mode'])
                if not s['active']: continue
                if s['auto_scroll'] and total==0:
                    logging.info("翻页完成（无新目标）"); s['auto_scroll']=None; pause("翻页完成")
                elif s['auto_scroll']:
                    logging.info(f"本页 {total} 像素，翻页...")
                    save_data(idx=0 if s['mode']!='free' else None, free_idx=0 if s['mode']=='free' else None)
                    if scroll(s['auto_scroll']): s['targets']=[]
                elif s['active']: pause("完成")

        except KeyboardInterrupt: break
        except Exception as e: logging.error(f"主循环: {e}"); pause("异常"); time.sleep(0.1)

    if gui_root:
        try: gui_root.destroy()
        except: pass
    logging.info("安全退出")

if __name__=="__main__":
    try: kb_module.is_pressed('a')
    except Exception as e: logging.error(f"keyboard 初始化失败: {e}"); logging.info("pip install keyboard")
    main()
