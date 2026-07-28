# Ensure the vibe rolling-context proxy is running (Windows).
# Pure stdlib on the Python side — no venv needed.
#
# PORTED from nestor-plugins/rolling-context 1.8.0 (frozen at ../upstream/start-proxy.ps1).
#
# WHAT WAS DROPPED, AND WHY IT MATTERS:
#   Upstream's first act was to rewrite ~/.claude/settings.json — inserting
#   ANTHROPIC_BASE_URL, chaining any pre-existing value into
#   ROLLING_CONTEXT_UPSTREAM, and seeding env defaults. ALL of that is gone here.
#   Vibe is configured by config.toml and has no settings.json, so porting the
#   block would have meant a launcher that edits a Claude Code file on every vibe
#   start. Redirect for vibe is a one-time [[providers]] entry, not a per-launch
#   rewrite; a launcher that mutates config on every run is also the thing most
#   likely to clobber `bypass_tool_permissions`.
#
# WHAT WAS KEPT VERBATIM (it was already right for this machine):
#   - the PID-file single-instance guard, including the PID-REUSE check: a saved
#     PID whose process is no longer python means the OS recycled the number, and
#     trusting it would leave the proxy dead while reporting it healthy.
#   - the uv interpreter resolution with `uv python install` fallback. This box has
#     no system python on PATH; upstream already wrote that path for exactly this case.
#
# WHAT CHANGED:
#   - all paths .claude -> .vibe
#   - port 5588 -> 5590 (a Claude-side proxy may hold 5588; 5589 is the GLM fork)
#   - version identity is now a CONTENT HASH of the proxy sources rather than a
#     plugin.json version string. There is no plugin.json here, and a hash means
#     editing server.py restarts the proxy on next launch instead of leaving a
#     stale process serving the old code — which is precisely how you spend an
#     afternoon debugging a fix that was never running.

$ErrorActionPreference = "SilentlyContinue"
$ScriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$ProxyDir  = Join-Path $ScriptDir "..\proxy"
$StateDir  = Join-Path $ScriptDir "..\state"
$LogDir    = Join-Path $env:USERPROFILE ".vibe\logs"

New-Item -ItemType Directory -Force -Path $StateDir | Out-Null
New-Item -ItemType Directory -Force -Path $LogDir   | Out-Null

$PidFile  = Join-Path $StateDir "proxy.pid"
$VerFile  = Join-Path $StateDir "proxy.version"
$HookLog  = Join-Path $LogDir "rolling-context-hook.log"
$ProxyLog = Join-Path $LogDir "rolling-context-proxy.log"

$Port = if ($env:ROLLING_CONTEXT_VIBE_PORT) { $env:ROLLING_CONTEXT_VIBE_PORT } else { "5590" }

function Log($msg) {
    $ts = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    Add-Content -Path $HookLog -Value "[$ts] $msg"
}

# Content hash over both proxy sources = the running code's identity.
$CurrentVersion = "unknown"
try {
    $srcs = @("vibe-rc-server.py", "compressor.py") | ForEach-Object { Join-Path $ProxyDir $_ }
    $blob = ($srcs | Where-Object { Test-Path $_ } | ForEach-Object { Get-Content $_ -Raw }) -join "`n"
    if ($blob) {
        $sha = [System.Security.Cryptography.SHA256]::Create()
        $bytes = $sha.ComputeHash([System.Text.Encoding]::UTF8.GetBytes($blob))
        $CurrentVersion = ([System.BitConverter]::ToString($bytes) -replace '-', '').Substring(0, 16).ToLower()
    }
} catch {
    Log "WARNING: could not hash proxy sources: $_"
}

Log "Launcher started. ProxyDir=$ProxyDir port=$Port version=$CurrentVersion"

# --- single instance -------------------------------------------------------
if (Test-Path $PidFile) {
    $savedPid = Get-Content $PidFile -ErrorAction SilentlyContinue
    if ($savedPid) {
        $proc = Get-Process -Id $savedPid -ErrorAction SilentlyContinue
        # PID reuse guard (kept from upstream): the number may now belong to
        # something else entirely.
        if ($proc -and $proc.ProcessName -notlike "python*") {
            Log "PID $savedPid is '$($proc.ProcessName)', not python - stale PID file"
            $proc = $null
        }
        if ($proc) {
            $runningVersion = if (Test-Path $VerFile) { Get-Content $VerFile -ErrorAction SilentlyContinue } else { "" }
            if ($runningVersion -eq $CurrentVersion) {
                Log "Proxy already running (PID $savedPid, $runningVersion)"
                exit 0
            }
            Log "Proxy source changed ($runningVersion -> $CurrentVersion), restarting PID $savedPid"
            Stop-Process -Id $savedPid -Force -ErrorAction SilentlyContinue
            Start-Sleep -Seconds 1
        }
    }
    Remove-Item $PidFile -Force -ErrorAction SilentlyContinue
    Remove-Item $VerFile -Force -ErrorAction SilentlyContinue
}

# --- interpreter -----------------------------------------------------------
# uv (astral.sh) manages Python on this box; there is no system python on PATH.
# Launch the uv-managed python.exe DIRECTLY so the PID file tracks the real proxy
# process rather than a `uv run` wrapper that exits.
$Python = $null
if (Get-Command uv -ErrorAction SilentlyContinue) {
    $Python = (& uv python find 2>$null | Select-Object -First 1)
    if (-not $Python -or -not (Test-Path $Python)) {
        Log "No uv-managed Python yet - running 'uv python install'..."
        & uv python install 2>$null | Out-Null
        $Python = (& uv python find 2>$null | Select-Object -First 1)
    }
}
if (-not $Python -or -not (Test-Path $Python)) {
    $Python = "python"   # only reachable on a box that does have system python
}

# Entry script is `vibe-rc-server.py`, NOT `server.py`. This is a real incident fix,
# not a style choice: the Claude-side rolling-context proxy ALSO runs a file called
# server.py, and this box routes Claude Code itself through it
# (ANTHROPIC_BASE_URL=127.0.0.1:5588). Any `pkill -f server.py`, or a PID mix-up
# between the two, kills the Anthropic path and every Claude session dies with
# ConnectionRefused mid-task. Measured: that is exactly what took down an audit run.
# Distinct filename means process lists and pattern-kills can tell them apart.
Log "Starting proxy with interpreter: $Python"
$proc = Start-Process -FilePath $Python -ArgumentList "vibe-rc-server.py" `
    -WorkingDirectory $ProxyDir `
    -RedirectStandardOutput $ProxyLog -RedirectStandardError "$ProxyLog.err" `
    -WindowStyle Hidden -PassThru

$proc.Id | Out-File -FilePath $PidFile -NoNewline
$CurrentVersion | Out-File -FilePath $VerFile -NoNewline
Log "Proxy started with PID $($proc.Id) ($CurrentVersion)"

exit 0
