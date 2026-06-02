import tkinter as tk
from tkinter import ttk, filedialog, messagebox, simpledialog
import threading
import time
import json
import os
import shutil
import struct
from collections import deque
import numpy as np
import pymem
import pyMeow as pme
import win32api
import win32con


# ========== BACKEND ==========
S = {   
    "aimbot_enabled": True,
    "aim_key": 0x02,
    "aim_mode": "Hold",      
    "is_aim_active": False,
    "method": "CamLock",
    "select_part": "Head",
    "smooth": 0.100,
    "predict": False,
    "predict_x": 0.000,
    
    "silent_aim": False,
    "trigger_enabled": False,
    "trigger_key": 0x12,
    "trigger_delay": 0.02,
    
    "box": True,
    "fov": True,
    "fov_radius": 100.0,
    "health": True,
    "skeleton": False
}

# Offsets
_ON = 176          
_OCH = 120         
_OLP = 312         
_OMI = 936         
_OHP = 404         
_OMH = 436         
_OPR = 328         
_OPS = 236         
_VE_PTR = 134140160   
_VM = 336             
_FDM = 2704           
_RDM = 464            

VIRTUAL_KEYS = {
    "RIGHT CLICK": 0x02, "LEFT CLICK": 0x01, "MIDDLE CLICK": 0x04,
    "SHIFT": 0x10, "CONTROL": 0x11, "ALT": 0x12, "SPACE": 0x20
}

TTL_GEN, TTL_PLAYER = 2.0, 1.5
R15_MIN = frozenset({"Head", "UpperTorso", "LowerTorso", "LeftHand", "RightHand", "LeftFoot", "RightFoot"})
R6_MIN = frozenset({"Head", "Torso", "Left Arm", "Right Arm", "Left Leg", "Right Leg"})

_CD, _CS, _CN, _CCL, _CCH, _CCR, _CP, _CDT = {}, {}, {}, {}, {}, {}, {}, {}
_CLP, _CPL = [0, 0.0], [[], 0.0]
_mono = time.monotonic

def _find_pid():
    for p in pymem.process.list_processes():
        try:
            if b"RobloxPlayerBeta.exe" in p.szExeFile: return p.th32ProcessID
        except Exception: pass
    return None

def _get_base(pid):
    from ctypes import c_size_t, c_void_p, byref, sizeof, windll
    h = windll.kernel32.OpenProcess(0x0410, False, pid)
    if not h: return None
    try:
        mods = (c_void_p * 1)()
        need = c_size_t()
        if windll.psapi.EnumProcessModules(h, byref(mods), sizeof(mods), byref(need)): return int(mods[0])
    finally: windll.kernel32.CloseHandle(h)
    return None

try:
    _pid = _find_pid()
    if _pid:
        _pm = pymem.Pymem(_pid)
        _base = _get_base(_pid)
        _RLL, _RF, _RI, _RB, _RSTR = _pm.read_longlong, _pm.read_float, _pm.read_int, _pm.read_bytes, _pm.read_string
        print(f"[Lotus] Attached: {hex(_base)}")
    else:
        print("[Lotus] Roblox not found")
        _base = None
except Exception as e:
    print(f"[Lotus] Attach failed: {e}")
    _base = None

def _drp(addr):
    if not addr or addr > 0x7FFFFFFFFFFF: return 0
    e = _CD.get(addr)
    if e and _mono() - e[1] < TTL_GEN: return e[0]
    try: v = _RLL(addr)
    except Exception: v = 0
    _CD[addr] = (v, _mono())
    return v

def _rbx_str(addr):
    if not addr: return ""
    e = _CS.get(addr)
    if e and _mono() - e[1] < TTL_GEN: return e[0]
    try:
        ln = _RI(addr + 0x10)
        p = _drp(addr) if ln > 15 else addr
        v = _RSTR(p, ln) if p else ""
    except Exception: v = ""
    _CS[addr] = (v, _mono())
    return v

def _name(inst):
    if not inst: return ""
    e = _CN.get(inst)
    if e and _mono() - e[1] < TTL_GEN: return e[0]
    v = _rbx_str(_drp(inst + _ON))
    _CN[inst] = (v, _mono())
    return v

def _classname(inst):
    if not inst: return ""
    e = _CCL.get(inst)
    if e and _mono() - e[1] < TTL_GEN: return e[0]
    try:
        p = _RLL(inst + 0x18)
        p = _RLL(p + 0x8)
        fl = _RLL(p + 0x18)
        if fl == 0x1F: p = _RLL(p)
        v = _rbx_str(p)
    except Exception: v = ""
    _CCL[inst] = (v, _mono())
    return v

def _children(inst):
    if not inst: return []
    now = _mono()
    e = _CCH.get(inst)
    if e and now - e[1] < TTL_GEN: return e[0]
    start = _drp(inst + _OCH)
    if not start: return []
    beg, end = _drp(start), _drp(start + 8)
    diff = end - beg
    if beg >= end or diff > 65536 or diff % 8 != 0: return []
    try:
        raw = _RB(beg, diff)
        v = np.frombuffer(raw, dtype=np.uint64)[0::2].tolist()
    except Exception: v = []
    _CCH[inst] = (v, now)
    return v

def _local_player(players):
    now = _mono()
    if now - _CLP[1] < TTL_PLAYER and _CLP[0]: return _CLP[0]
    try: v = _RLL(players + _OLP)
    except Exception: v = 0
    _CLP[0], _CLP[1] = v, now
    return v

def _character(player):
    if not player: return 0
    now = _mono()
    e = _CCR.get(player)
    if e and now - e[1] < 1.0: return e[0]
    try: v = _RLL(player + _OMI)
    except Exception: v = 0
    _CCR[player] = (v, now)
    return v

def _pos(part):
    if not part: return None
    now = _mono()
    e = _CP.get(part)
    prim = e[0] if (e and now - e[1] < TTL_GEN) else None
    if prim is None:
        try: prim = _RLL(part + _OPR)
        except Exception: return None
        _CP[part] = (prim, now)
    if not prim: return None
    try: return struct.unpack("<3f", _RB(prim + _OPS, 12))
    except Exception: return None

def _chardata(char):
    if not char: return {}
    e = _CDT.get(char)
    if e: return e
    kids = _children(char)
    if not kids: return {}
    knames = [_name(k) for k in kids]
    r15 = "UpperTorso" in knames
    parts = {nm: inst for inst, nm in zip(kids, knames) if nm in (R15_MIN if r15 else R6_MIN)}
    hum = 0
    for ch in kids:
        if _classname(ch) == "Humanoid":
            hum = ch; break
    if not hum or not parts: return {}
    e = {"parts": parts, "hum": hum}
    _CDT[char] = e
    return e

def CoreAutomationEngine():
    if not _base: return
    
    sw, sh = win32api.GetSystemMetrics(0), win32api.GetSystemMetrics(1)
    hw, hh = sw * 0.5, sh * 0.5
    pme.overlay_init(title="Lotus Overlay", fps=0, exitKey=0x23)
    
    ve = 0
    while ve == 0:
        try:
            ve = _RLL(_base + _VE_PTR)
            if ve == 0:
                time.sleep(1)
        except:
            time.sleep(1)
    
    mta = ve + _VM
    
    while True:
        try:
            fdm = _RLL(ve + _FDM)
            dm = _RLL(fdm + _RDM)
            plrs = 0
            for ch in _children(dm):
                if _classname(ch) == "Players":
                    plrs = ch
                    break
            if plrs != 0:
                break
        except:
            pass
        time.sleep(1)

    while pme.overlay_loop():
        try:
            vm = np.frombuffer(_RB(mta, 64), dtype=np.float32).reshape(4, 4)
            pme.begin_drawing()
            
            lp = _local_player(plrs)
            cur = win32api.GetCursorPos()
            
            if S["fov"]:
                pme.draw_circle_lines(cur[0], cur[1], int(S["fov_radius"]), pme.get_color("cyan"))
                
            now = _mono()
            if now - _CPL[1] > TTL_PLAYER:
                _CPL[0], _CPL[1] = _children(plrs), now
            
            best_target = None
            closest_cursor_dist = float('inf')
            trigger_ready = False

            for player in _CPL[0]:
                if player == lp: continue
                char = _character(player)
                if not char: continue
                cd = _chardata(char)
                if not cd: continue
                
                try: hp = _RF(cd["hum"] + _OHP)
                except: continue
                if hp <= 0: continue
                
                parts = cd["parts"]
                lock_node = S["select_part"] if S["select_part"] in parts else ("Head" if "Head" in parts else None)
                if not lock_node: continue
                
                p3d = _pos(parts[lock_node])
                if not p3d: continue
                
                clip = np.array([p3d[0], p3d[1], p3d[2], 1.0]) @ vm.T
                if clip[3] < 1e-4: continue
                inv_w = 1.0 / clip[3]
                sx = int((clip[0] * inv_w + 1.0) * hw)
                sy = int((1.0 - clip[1] * inv_w) * hh)
                
                box_w = 24
                box_h = 36
                bx = sx - (box_w // 2)
                by = sy - 18
                
                if S["box"]:
                    pme.draw_rectangle_lines(bx, by, box_w, box_h, pme.get_color("cyan"), 1.0)
                
                if S["health"]:
                    try: max_hp = _RF(cd["hum"] + _OMH)
                    except: max_hp = 100.0
                    pct = max(0.0, min(1.0, hp / max_hp)) if max_hp > 0 else 0
                    hp_color = pme.get_color("green") if pct > 0.5 else (pme.get_color("orange") if pct > 0.25 else pme.get_color("red"))
                    bar_x = bx - 6
                    bar_y = by
                    bar_h = int(box_h * pct)
                    pme.draw_rectangle(bar_x, bar_y, 3, box_h, pme.get_color("black"))
                    pme.draw_rectangle(bar_x, bar_y + (box_h - bar_h), 3, bar_h, hp_color)
                
                d_cur = np.hypot(sx - cur[0], sy - cur[1])
                if d_cur <= S["fov_radius"] and d_cur < closest_cursor_dist:
                    closest_cursor_dist = d_cur
                    best_target = (sx, sy)
                
                crosshair_dist = np.hypot(sx - hw, sy - hh)
                if crosshair_dist <= 15.0 and clip[3] > 0.1:
                    trigger_ready = True

            S["is_aim_active"] = bool(win32api.GetAsyncKeyState(S["aim_key"]) & 0x8000)

            if S["aimbot_enabled"] and best_target and S["is_aim_active"]:
                dx, dy = best_target[0] - cur[0], best_target[1] - cur[1]
                if S["method"] == "CamLock":
                    mx, my = int(dx * (S["smooth"] + 0.01)), int(dy * (S["smooth"] + 0.01))
                    if mx != 0 or my != 0:
                        win32api.mouse_event(win32con.MOUSEEVENTF_MOVE, mx, my, 0, 0)
                else:
                    win32api.SetCursorPos((int(cur[0] + dx * 0.08), int(cur[1] + dy * 0.08)))

            if S["trigger_enabled"] and trigger_ready:
                if win32api.GetAsyncKeyState(S["trigger_key"]) & 0x8000:
                    time.sleep(S["trigger_delay"])
                    win32api.mouse_event(win32con.MOUSEEVENTF_LEFTDOWN, 0, 0, 0, 0)
                    time.sleep(0.005)
                    win32api.mouse_event(win32con.MOUSEEVENTF_LEFTUP, 0, 0, 0, 0)

            pme.end_drawing()
        except Exception:
            pass
        time.sleep(0.001)


# ========== CONFIG MANAGER ==========
class ConfigManager:
    def __init__(self):
        self.config_dir = "lotus_configs"
        self.current_profile = "default"
        
        if not os.path.exists(self.config_dir):
            os.makedirs(self.config_dir)
        
        self.save_profile("default", S)
    
    def get_profiles(self):
        profiles = []
        if os.path.exists(self.config_dir):
            for file in os.listdir(self.config_dir):
                if file.endswith(".json"):
                    profiles.append(file[:-5])
        return sorted(profiles)
    
    def save_profile(self, name, settings):
        try:
            save_data = {k: v for k, v in settings.items() if k != "is_aim_active"}
            filepath = os.path.join(self.config_dir, f"{name}.json")
            with open(filepath, 'w') as f:
                json.dump(save_data, f, indent=4)
            return True, f"Saved to '{name}'"
        except Exception as e:
            return False, f"Failed: {e}"
    
    def load_profile(self, name, target_dict):
        try:
            filepath = os.path.join(self.config_dir, f"{name}.json")
            with open(filepath, 'r') as f:
                loaded = json.load(f)
            
            for key, value in loaded.items():
                if key in target_dict and key != "is_aim_active":
                    target_dict[key] = value
            
            self.current_profile = name
            return True, f"Loaded '{name}'"
        except Exception as e:
            return False, f"Failed: {e}"
    
    def delete_profile(self, name):
        try:
            if name == "default":
                return False, "Cannot delete default profile"
            
            filepath = os.path.join(self.config_dir, f"{name}.json")
            if os.path.exists(filepath):
                os.remove(filepath)
                
                if self.current_profile == name:
                    self.load_profile("default", S)
                    self.current_profile = "default"
                
                return True, f"Deleted '{name}'"
            return False, f"Profile '{name}' not found"
        except Exception as e:
            return False, f"Failed: {e}"
    
    def export_profile(self, name):
        try:
            source = os.path.join(self.config_dir, f"{name}.json")
            if not os.path.exists(source):
                return False, f"Profile '{name}' not found"
            
            dest = filedialog.asksaveasfilename(
                defaultextension=".json",
                filetypes=[("JSON files", "*.json"), ("All files", "*.*")],
                initialfile=f"{name}_export.json"
            )
            
            if dest:
                shutil.copy(source, dest)
                return True, f"Exported to {os.path.basename(dest)}"
            return False, "Export cancelled"
        except Exception as e:
            return False, f"Export failed: {e}"
    
    def import_profile(self):
        try:
            filepath = filedialog.askopenfilename(
                filetypes=[("JSON files", "*.json"), ("All files", "*.*")]
            )
            
            if filepath:
                name = os.path.basename(filepath).replace(".json", "")
                
                if os.path.exists(os.path.join(self.config_dir, f"{name}.json")):
                    result = messagebox.askyesno(
                        "Profile Exists",
                        f"Profile '{name}' already exists. Overwrite?"
                    )
                    if not result:
                        return False, "Import cancelled"
                
                dest = os.path.join(self.config_dir, f"{name}.json")
                shutil.copy(filepath, dest)
                return True, f"Imported '{name}'"
            
            return False, "Import cancelled"
        except Exception as e:
            return False, f"Import failed: {e}"


# ========== UI (DEFAULT WINDOWS TITLE BAR) ==========
class LotusUI:
    def __init__(self):
        self.root = tk.Tk()
        self.root.title("lotus")
        self.root.geometry("400x540")
        self.root.resizable(False, False)
        self.root.configure(bg="#0a0e17")
        
        # DEFAULT Windows title bar - alt+tab works!
        # No overrideredirect, no custom buttons
        
        self.config_manager = ConfigManager()
        
        # Main container
        self.main_frame = tk.Frame(self.root, bg="#0a0e17")
        self.main_frame.pack(fill=tk.BOTH, expand=True, padx=2, pady=(0, 2))
        
        self.create_notebook()
        self.create_aimbot_tab()
        self.create_visuals_tab()
        self.create_config_tab()
        
        self.status_var = tk.StringVar(value="● READY")
        self.status_bar = tk.Label(
            self.root, textvariable=self.status_var, 
            bg="#0e121c", fg="#2a9d8f", font=("Segoe UI", 9),
            anchor=tk.W, padx=12, pady=6
        )
        self.status_bar.pack(side=tk.BOTTOM, fill=tk.X)
        
        self.listening_for = None
        
        self.update_ui_from_s()
        self.refresh_profile_list()
        
    def update_ui_from_s(self):
        try:
            self.aim_enabled.set(S.get("aimbot_enabled", True))
            self.smooth_var.set(S.get("smooth", 0.1))
            self.smooth_label.config(text=f"{S.get('smooth', 0.1):.2f}")
            self.fov_var.set(S.get("fov_radius", 100))
            self.fov_label.config(text=str(int(S.get("fov_radius", 100))))
            self.method_var.set(S.get("method", "CamLock"))
            self.part_var.set(S.get("select_part", "Head"))
            self.silent_aim.set(S.get("silent_aim", False))
            self.trigger_enabled.set(S.get("trigger_enabled", False))
            self.box_esp.set(S.get("box", True))
            self.health_bars.set(S.get("health", True))
            self.fov_circle.set(S.get("fov", True))
            
            aim_key_name = [k for k, v in VIRTUAL_KEYS.items() if v == S.get("aim_key", 0x02)]
            if aim_key_name:
                self.aim_key_btn.config(text=aim_key_name[0])
            
            trigger_key_name = [k for k, v in VIRTUAL_KEYS.items() if v == S.get("trigger_key", 0x12)]
            if trigger_key_name:
                self.trigger_key_btn.config(text=trigger_key_name[0])
            
            self.delay_var.set(S.get("trigger_delay", 0.02) * 1000)
            self.delay_label.config(text=str(int(S.get("trigger_delay", 0.02) * 1000)))
            
            self.status_var.set(f"● LOADED: {self.config_manager.current_profile}")
        except Exception as e:
            pass
    
    def refresh_profile_list(self):
        profiles = self.config_manager.get_profiles()
        self.profile_combo['values'] = profiles
        if self.config_manager.current_profile in profiles:
            self.profile_combo.set(self.config_manager.current_profile)
        else:
            self.profile_combo.set("default")
    
    def create_notebook(self):
        style = ttk.Style()
        style.theme_use('clam')
        style.configure("TNotebook", background="#0a0e17", borderwidth=0)
        style.configure("TNotebook.Tab", background="#151b26", foreground="#8a95a5", 
                       padding=[16, 6], font=("Segoe UI", 10, "bold"))
        style.map("TNotebook.Tab", background=[("selected", "#1e2738"), ("active", "#1a2130")],
                 foreground=[("selected", "#2a9d8f"), ("active", "#b0bed0")])
        
        self.notebook = ttk.Notebook(self.main_frame)
        self.notebook.pack(fill=tk.BOTH, expand=True, padx=8, pady=8)
        
    def create_aimbot_tab(self):
        tab = tk.Frame(self.notebook, bg="#0e121c")
        self.notebook.add(tab, text="aim")
        
        card1 = tk.Frame(tab, bg="#0e121c")
        card1.pack(fill=tk.X, pady=(0, 12))
        
        self.aim_enabled = tk.BooleanVar(value=True)
        tk.Checkbutton(
            card1, text="enable aimbot", variable=self.aim_enabled,
            bg="#0e121c", fg="#c0cbd8", selectcolor="#0e121c",
            font=("Segoe UI", 10), anchor=tk.W, padx=12, pady=6,
            command=self.on_aim_toggle
        ).pack(fill=tk.X)
        
        key_frame = tk.Frame(card1, bg="#0e121c")
        key_frame.pack(fill=tk.X, padx=12, pady=4)
        tk.Label(key_frame, text="aim key", bg="#0e121c", fg="#8a95a5", font=("Segoe UI", 9)).pack(side=tk.LEFT)
        self.aim_key_btn = tk.Button(
            key_frame, text="RIGHT CLICK", bg="#151b26", fg="#2a9d8f",
            font=("Segoe UI", 8), relief=tk.FLAT, padx=10, pady=2,
            command=self.bind_aim_key
        )
        self.aim_key_btn.pack(side=tk.RIGHT)
        
        method_frame = tk.Frame(card1, bg="#0e121c")
        method_frame.pack(fill=tk.X, padx=12, pady=4)
        tk.Label(method_frame, text="method", bg="#0e121c", fg="#8a95a5", font=("Segoe UI", 9)).pack(side=tk.LEFT)
        self.method_var = tk.StringVar(value="CamLock")
        method_menu = ttk.Combobox(method_frame, textvariable=self.method_var, values=["CamLock", "Smooth"],
                                   width=12, state="readonly")
        method_menu.pack(side=tk.RIGHT)
        method_menu.bind("<<ComboboxSelected>>", self.on_method_change)
        
        part_frame = tk.Frame(card1, bg="#0e121c")
        part_frame.pack(fill=tk.X, padx=12, pady=4)
        tk.Label(part_frame, text="target", bg="#0e121c", fg="#8a95a5", font=("Segoe UI", 9)).pack(side=tk.LEFT)
        self.part_var = tk.StringVar(value="Head")
        part_menu = ttk.Combobox(part_frame, textvariable=self.part_var, values=["Head", "UpperTorso", "LowerTorso"],
                                 width=12, state="readonly")
        part_menu.pack(side=tk.RIGHT)
        part_menu.bind("<<ComboboxSelected>>", self.on_part_change)
        
        card2 = tk.Frame(tab, bg="#0e121c")
        card2.pack(fill=tk.X, pady=(0, 12))
        
        smooth_frame = tk.Frame(card2, bg="#0e121c")
        smooth_frame.pack(fill=tk.X, padx=12, pady=6)
        tk.Label(smooth_frame, text="smoothness", bg="#0e121c", fg="#8a95a5", font=("Segoe UI", 9)).pack(side=tk.LEFT)
        self.smooth_var = tk.DoubleVar(value=0.1)
        self.smooth_label = tk.Label(smooth_frame, text="0.10", bg="#0e121c", fg="#2a9d8f", font=("Segoe UI", 9))
        self.smooth_label.pack(side=tk.RIGHT, padx=6)
        smooth_slider = tk.Scale(
            card2, from_=0.01, to=0.5, resolution=0.01, orient=tk.HORIZONTAL,
            variable=self.smooth_var, bg="#0e121c", fg="#2a9d8f", highlightthickness=0,
            troughcolor="#1e2738", activebackground="#2a9d8f", length=340
        )
        smooth_slider.pack(padx=12, pady=(0, 8))
        smooth_slider.bind("<ButtonRelease-1>", self.on_smooth_change)
        
        fov_frame = tk.Frame(card2, bg="#0e121c")
        fov_frame.pack(fill=tk.X, padx=12, pady=6)
        tk.Label(fov_frame, text="fov radius", bg="#0e121c", fg="#8a95a5", font=("Segoe UI", 9)).pack(side=tk.LEFT)
        self.fov_var = tk.DoubleVar(value=100)
        self.fov_label = tk.Label(fov_frame, text="100", bg="#0e121c", fg="#2a9d8f", font=("Segoe UI", 9))
        self.fov_label.pack(side=tk.RIGHT, padx=6)
        fov_slider = tk.Scale(
            card2, from_=50, to=300, resolution=5, orient=tk.HORIZONTAL,
            variable=self.fov_var, bg="#0e121c", fg="#2a9d8f", highlightthickness=0,
            troughcolor="#1e2738", activebackground="#2a9d8f", length=340
        )
        fov_slider.pack(padx=12, pady=(0, 8))
        fov_slider.bind("<ButtonRelease-1>", self.on_fov_change)
        
        card3 = tk.Frame(tab, bg="#0e121c")
        card3.pack(fill=tk.X)
        
        self.silent_aim = tk.BooleanVar(value=False)
        tk.Checkbutton(
            card3, text="silent aim", variable=self.silent_aim,
            bg="#0e121c", fg="#c0cbd8", selectcolor="#0e121c",
            font=("Segoe UI", 9), anchor=tk.W, padx=12, pady=2,
            command=self.on_silent_toggle
        ).pack(fill=tk.X)
        
        self.trigger_enabled = tk.BooleanVar(value=False)
        tk.Checkbutton(
            card3, text="triggerbot", variable=self.trigger_enabled,
            bg="#0e121c", fg="#c0cbd8", selectcolor="#0e121c",
            font=("Segoe UI", 9), anchor=tk.W, padx=12, pady=2,
            command=self.on_trigger_toggle
        ).pack(fill=tk.X)
        
    def create_visuals_tab(self):
        tab = tk.Frame(self.notebook, bg="#0e121c")
        self.notebook.add(tab, text="visuals")
        
        self.box_esp = tk.BooleanVar(value=True)
        tk.Checkbutton(
            tab, text="box esp", variable=self.box_esp,
            bg="#0e121c", fg="#c0cbd8", selectcolor="#0e121c",
            font=("Segoe UI", 10), anchor=tk.W, padx=20, pady=6,
            command=self.on_box_toggle
        ).pack(fill=tk.X)
        
        self.health_bars = tk.BooleanVar(value=True)
        tk.Checkbutton(
            tab, text="health bars", variable=self.health_bars,
            bg="#0e121c", fg="#c0cbd8", selectcolor="#0e121c",
            font=("Segoe UI", 10), anchor=tk.W, padx=20, pady=6,
            command=self.on_health_toggle
        ).pack(fill=tk.X)
        
        self.fov_circle = tk.BooleanVar(value=True)
        tk.Checkbutton(
            tab, text="fov circle", variable=self.fov_circle,
            bg="#0e121c", fg="#c0cbd8", selectcolor="#0e121c",
            font=("Segoe UI", 10), anchor=tk.W, padx=20, pady=6,
            command=self.on_fov_circle_toggle
        ).pack(fill=tk.X)
        
    def create_config_tab(self):
        tab = tk.Frame(self.notebook, bg="#0e121c")
        self.notebook.add(tab, text="config")
        
        profile_frame = tk.Frame(tab, bg="#0e121c")
        profile_frame.pack(fill=tk.X, padx=12, pady=12)
        
        tk.Label(profile_frame, text="profile", bg="#0e121c", fg="#8a95a5", font=("Segoe UI", 9)).pack(side=tk.LEFT)
        
        self.profile_combo = ttk.Combobox(profile_frame, values=[], width=15, state="readonly")
        self.profile_combo.pack(side=tk.RIGHT)
        
        btn_frame1 = tk.Frame(tab, bg="#0e121c")
        btn_frame1.pack(fill=tk.X, padx=12, pady=6)
        
        save_btn = tk.Button(
            btn_frame1, text="save current", bg="#151b26", fg="#2a9d8f",
            font=("Segoe UI", 9), relief=tk.FLAT, padx=12, pady=4,
            command=self.save_current_profile
        )
        save_btn.pack(side=tk.LEFT, expand=True, fill=tk.X, padx=2)
        
        load_btn = tk.Button(
            btn_frame1, text="load selected", bg="#151b26", fg="#2a9d8f",
            font=("Segoe UI", 9), relief=tk.FLAT, padx=12, pady=4,
            command=self.load_selected_profile
        )
        load_btn.pack(side=tk.LEFT, expand=True, fill=tk.X, padx=2)
        
        delete_btn = tk.Button(
            btn_frame1, text="delete selected", bg="#151b26", fg="#e06c75",
            font=("Segoe UI", 9), relief=tk.FLAT, padx=12, pady=4,
            command=self.delete_selected_profile
        )
        delete_btn.pack(side=tk.LEFT, expand=True, fill=tk.X, padx=2)
        
        btn_frame2 = tk.Frame(tab, bg="#0e121c")
        btn_frame2.pack(fill=tk.X, padx=12, pady=6)
        
        new_btn = tk.Button(
            btn_frame2, text="new profile", bg="#151b26", fg="#61afef",
            font=("Segoe UI", 9), relief=tk.FLAT, padx=12, pady=4,
            command=self.new_profile
        )
        new_btn.pack(side=tk.LEFT, expand=True, fill=tk.X, padx=2)
        
        export_btn = tk.Button(
            btn_frame2, text="export selected", bg="#151b26", fg="#98c379",
            font=("Segoe UI", 9), relief=tk.FLAT, padx=12, pady=4,
            command=self.export_profile
        )
        export_btn.pack(side=tk.LEFT, expand=True, fill=tk.X, padx=2)
        
        import_btn = tk.Button(
            btn_frame2, text="import profile", bg="#151b26", fg="#e5c07b",
            font=("Segoe UI", 9), relief=tk.FLAT, padx=12, pady=4,
            command=self.import_profile
        )
        import_btn.pack(side=tk.LEFT, expand=True, fill=tk.X, padx=2)
        
        sep = tk.Frame(tab, bg="#1e2738", height=1)
        sep.pack(fill=tk.X, padx=12, pady=12)
        
        tk.Label(tab, text="trigger settings", bg="#0e121c", fg="#2a9d8f", 
                font=("Segoe UI", 10, "bold"), anchor=tk.W).pack(fill=tk.X, padx=12, pady=(0, 6))
        
        key_frame = tk.Frame(tab, bg="#0e121c")
        key_frame.pack(fill=tk.X, padx=12, pady=6)
        tk.Label(key_frame, text="trigger key", bg="#0e121c", fg="#8a95a5", font=("Segoe UI", 9)).pack(side=tk.LEFT)
        self.trigger_key_btn = tk.Button(
            key_frame, text="ALT", bg="#151b26", fg="#2a9d8f",
            font=("Segoe UI", 8), relief=tk.FLAT, padx=10, pady=2,
            command=self.bind_trigger_key
        )
        self.trigger_key_btn.pack(side=tk.RIGHT)
        
        delay_frame = tk.Frame(tab, bg="#0e121c")
        delay_frame.pack(fill=tk.X, padx=12, pady=6)
        tk.Label(delay_frame, text="trigger delay (ms)", bg="#0e121c", fg="#8a95a5", font=("Segoe UI", 9)).pack(side=tk.LEFT)
        self.delay_var = tk.DoubleVar(value=20)
        self.delay_label = tk.Label(delay_frame, text="20", bg="#0e121c", fg="#2a9d8f", font=("Segoe UI", 9))
        self.delay_label.pack(side=tk.RIGHT, padx=6)
        delay_slider = tk.Scale(
            tab, from_=0, to=200, resolution=5, orient=tk.HORIZONTAL,
            variable=self.delay_var, bg="#0e121c", fg="#2a9d8f", highlightthickness=0,
            troughcolor="#1e2738", activebackground="#2a9d8f", length=350
        )
        delay_slider.pack(padx=12, pady=(0, 12))
        delay_slider.bind("<ButtonRelease-1>", self.on_delay_change)
        
    def save_current_profile(self):
        name = self.profile_combo.get()
        if not name or name == "":
            self.new_profile()
            return
        
        success, msg = self.config_manager.save_profile(name, S)
        self.status_var.set(f"● {msg}")
        self.refresh_profile_list()
        if success:
            self.config_manager.current_profile = name
    
    def load_selected_profile(self):
        name = self.profile_combo.get()
        if not name:
            self.status_var.set("● No profile selected")
            return
        
        success, msg = self.config_manager.load_profile(name, S)
        if success:
            self.update_ui_from_s()
        self.status_var.set(f"● {msg}")
    
    def delete_selected_profile(self):
        name = self.profile_combo.get()
        if not name:
            return
        
        if messagebox.askyesno("Delete Profile", f"Delete '{name}'?"):
            success, msg = self.config_manager.delete_profile(name)
            self.status_var.set(f"● {msg}")
            self.refresh_profile_list()
            if success:
                self.update_ui_from_s()
    
    def new_profile(self):
        name = simpledialog.askstring("New Profile", "Enter profile name:")
        if name and name.strip():
            name = name.strip()
            name = "".join(c for c in name if c.isalnum() or c in " _-")
            if name:
                success, msg = self.config_manager.save_profile(name, S)
                if success:
                    self.refresh_profile_list()
                    self.profile_combo.set(name)
                    self.config_manager.current_profile = name
                self.status_var.set(f"● {msg}")
    
    def export_profile(self):
        name = self.profile_combo.get()
        if not name:
            self.status_var.set("● No profile selected")
            return
        
        success, msg = self.config_manager.export_profile(name)
        self.status_var.set(f"● {msg}")
    
    def import_profile(self):
        success, msg = self.config_manager.import_profile()
        if success:
            self.refresh_profile_list()
        self.status_var.set(f"● {msg}")
    
    def on_aim_toggle(self):
        S["aimbot_enabled"] = self.aim_enabled.get()
        
    def on_smooth_change(self, e):
        self.smooth_label.config(text=f"{self.smooth_var.get():.2f}")
        S["smooth"] = self.smooth_var.get()
        
    def on_fov_change(self, e):
        self.fov_label.config(text=str(int(self.fov_var.get())))
        S["fov_radius"] = self.fov_var.get()
        
    def on_method_change(self, e):
        S["method"] = self.method_var.get()
        
    def on_part_change(self, e):
        S["select_part"] = self.part_var.get()
        
    def on_silent_toggle(self):
        S["silent_aim"] = self.silent_aim.get()
        
    def on_trigger_toggle(self):
        S["trigger_enabled"] = self.trigger_enabled.get()
        
    def on_box_toggle(self):
        S["box"] = self.box_esp.get()
        
    def on_health_toggle(self):
        S["health"] = self.health_bars.get()
        
    def on_fov_circle_toggle(self):
        S["fov"] = self.fov_circle.get()
        
    def on_delay_change(self, e):
        self.delay_label.config(text=str(int(self.delay_var.get())))
        S["trigger_delay"] = self.delay_var.get() / 1000
        
    def bind_aim_key(self):
        self.aim_key_btn.config(text="...", fg="#e06c75")
        self.listening_for = "aim"
        self.root.bind("<Key>", self.capture_key)
        self.root.bind("<Button-1>", self.capture_mouse, add=True)
        
    def bind_trigger_key(self):
        self.trigger_key_btn.config(text="...", fg="#e06c75")
        self.listening_for = "trigger"
        self.root.bind("<Key>", self.capture_key)
        self.root.bind("<Button-1>", self.capture_mouse, add=True)
        
    def capture_key(self, e):
        name = e.keysym.upper()
        if name == "SPACE": name = "SPACE"
        elif "CONTROL" in name: name = "CONTROL"
        elif "SHIFT" in name: name = "SHIFT"
        elif "ALT" in name: name = "ALT"
        
        v_code = VIRTUAL_KEYS.get(name, 0)
        
        if self.listening_for == "aim":
            self.aim_key_btn.config(text=name, fg="#2a9d8f")
            if v_code:
                S["aim_key"] = v_code
        else:
            self.trigger_key_btn.config(text=name, fg="#2a9d8f")
            if v_code:
                S["trigger_key"] = v_code
                
        self.root.unbind("<Key>")
        self.root.unbind("<Button-1>")
        self.listening_for = None
        
    def capture_mouse(self, e):
        if e.widget == self.aim_key_btn or e.widget == self.trigger_key_btn:
            return
            
        name = ""
        if e.num == 1: name = "LEFT CLICK"
        elif e.num == 2: name = "MIDDLE CLICK"
        elif e.num == 3: name = "RIGHT CLICK"
        
        if name:
            v_code = VIRTUAL_KEYS.get(name, 0)
            if self.listening_for == "aim":
                self.aim_key_btn.config(text=name, fg="#2a9d8f")
                S["aim_key"] = v_code
            else:
                self.trigger_key_btn.config(text=name, fg="#2a9d8f")
                S["trigger_key"] = v_code
                
            self.root.unbind("<Key>")
            self.root.unbind("<Button-1>")
            self.listening_for = None
        
    def run(self):
        self.root.mainloop()


if __name__ == "__main__":
    threading.Thread(target=CoreAutomationEngine, daemon=True).start()
    ui = LotusUI()
    ui.run()