#!/usr/bin/env python3
"""
给 `lake build` 加一个进度条。

用法（在 Lean 项目根目录下）：
    python3 lake_progress.py                 # 等同于 lake build
    python3 lake_progress.py MyProject.Foo   # 额外参数原样传给 lake build
    python3 lake_progress.py --show-sorry    # 也显示 "declaration uses 'sorry'" 警告（默认隐藏）

完整日志会保存到 lake_build.log；错误和警告会实时打印在进度条上方。

注意：本脚本运行的是真正的 `lake build`。在多会话协作期间（leader 的安装窗口、worker 的 verify 正在运行时）
不要运行，否则两个构建会争用同一批 .olean 文件和内存。
"""
import re
import shutil
import subprocess
import sys
import time
import unicodedata

ANSI = re.compile(r"\x1b\[[0-9;]*[A-Za-z]")
JOB = re.compile(r"\[(\d+)/(\d+)\]")          # Lake 输出里的 [已完成/总数]
IMPORTANT = re.compile(r"error|✖|warning|⚠", re.IGNORECASE)
SORRY = re.compile(r"declaration uses 'sorry'")
ETA_WINDOW = 120.0                             # 用最近这么多秒的速度估计剩余时间


def fmt_time(sec: float) -> str:
    sec = int(sec)
    h, rem = divmod(sec, 3600)
    m, s = divmod(rem, 60)
    return f"{h}:{m:02d}:{s:02d}" if h else f"{m:02d}:{s:02d}"


def disp_width(s: str) -> int:
    """终端显示宽度：中文等全角字符占 2 列。"""
    return sum(2 if unicodedata.east_asian_width(c) in ("W", "F") else 1 for c in s)


def clip(s: str, width: int) -> str:
    """按显示宽度截断字符串。"""
    out, w = [], 0
    for c in s:
        cw = 2 if unicodedata.east_asian_width(c) in ("W", "F") else 1
        if w + cw > width:
            break
        out.append(c)
        w += cw
    return "".join(out)


def eta_seconds(samples: list, done: int, total: int) -> float:
    """按最近 ETA_WINDOW 秒内的完成速度估计剩余时间（已缓存模块瞬间完成，不应拉低估计）。"""
    if len(samples) < 2 or done >= total:
        return 0.0
    t0, d0 = samples[0]
    t1, d1 = samples[-1]
    if t1 <= t0 or d1 <= d0:
        return 0.0
    rate = (d1 - d0) / (t1 - t0)
    return (total - done) / rate


def draw(done: int, total: int, start: float, eta: float, current: str) -> None:
    cols = shutil.get_terminal_size((100, 20)).columns
    elapsed = time.time() - start
    frac = done / total if total else 0.0
    info = f" {done}/{total} {frac*100:5.1f}% 用时 {fmt_time(elapsed)} 剩余 ~{fmt_time(eta)} "
    width = max(10, min(40, cols - disp_width(info) - 30))
    filled = int(width * frac)
    bar = "█" * filled + "░" * (width - filled)
    room = cols - (width + 2) - disp_width(info) - 1   # 留 1 列，避免自动换行
    name = clip(current, max(0, room))
    sys.stderr.write(f"\r\x1b[K[{bar}]{info}{name}")
    sys.stderr.flush()


def main() -> int:
    # Windows 中文控制台默认 GBK，"✅"、"█" 等字符会触发 UnicodeEncodeError
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(encoding="utf-8", errors="replace")
        except (AttributeError, ValueError):
            pass

    args = sys.argv[1:]
    show_sorry = "--show-sorry" in args
    args = [a for a in args if a != "--show-sorry"]
    cmd = ["lake", "build", *args]
    start = time.time()
    done, total, current = 0, 0, ""
    samples: list = []                           # (时间, 已完成数)，用于 ETA

    with open("lake_build.log", "w", encoding="utf-8") as log:
        try:
            proc = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                encoding="utf-8",
                errors="replace",
                bufsize=1,
            )
        except FileNotFoundError:
            print("❌ 找不到 lake：请确认 elan/lake 在 PATH 中，并在项目根目录下运行。")
            return 127
        assert proc.stdout is not None
        try:
            for raw in proc.stdout:
                line = ANSI.sub("", raw.rstrip("\n"))
                log.write(line + "\n")

                # 错误/警告打印在进度条上方（包括 Lake 自己的 "✖ [n/m] …" / "⚠ [n/m] …" 状态行）
                if IMPORTANT.search(line) and (show_sorry or not SORRY.search(line)):
                    sys.stderr.write("\r\x1b[K" + line + "\n")

                m = JOB.search(line)
                if m:
                    done, total = int(m.group(1)), int(m.group(2))
                    current = line[m.end():].strip()
                    now = time.time()
                    samples.append((now, done))
                    while samples and now - samples[0][0] > ETA_WINDOW:
                        samples.pop(0)

                if total:
                    draw(done, total, start, eta_seconds(samples, done, total), current)

            code = proc.wait()
        except KeyboardInterrupt:
            proc.terminate()
            proc.wait()
            sys.stderr.write("\n")
            print("⏹ 已中断，完整日志见 lake_build.log")
            return 130

    sys.stderr.write("\n")
    status = "✅ 构建成功" if code == 0 else f"❌ 构建失败（退出码 {code}）"
    print(f"{status}，总用时 {fmt_time(time.time() - start)}，完整日志见 lake_build.log")
    return code


if __name__ == "__main__":
    sys.exit(main())
