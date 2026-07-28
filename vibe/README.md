# rolling-context for Vibe Code — vendored port

Self-contained. Nothing here reads `~/.claude/plugins/cache/nestor-plugins/`;
that tree can be edited, moved, or deleted without affecting vibe. Same rule as
the caveman vendoring (`~/.vibe/caveman/README.md`).

Ported from nestor-plugins/rolling-context **1.8.0**.

## Before you change anything

Two gates guard this plugin. Both must pass before any edit ships; read the exit
code directly, never through a pipe.

```bash
cd ~/.vibe/nestor-plugins/rolling-context/proxy
PYTHONIOENCODING=utf-8 uv run --no-project python check-compressor-drift.py
#   expect: CLEAN, exit 0
cd /d/Lean/proofs && lake build Proofs.Compressor
#   expect: exit 0, 0 sorry
```

There is **no bare `python`, `python3`, or `py` on PATH** on this machine — verified,
not assumed. `uv` is on PATH and the line above was executed as written. If `uv` is
ever absent, the vibe-bundled interpreter works and is tied to the tool this plugin
serves: `~/AppData/Roaming/uv/tools/mistral-vibe/Scripts/python.exe`. `lake` comes
from `~/.elan/bin`, already on PATH.

The drift checker executes the behavioural invariants rather than reading them, and
the Python corpus is compiled into Lean `rfl` specs — so a Python/Lean disagreement
fails the **build**, not just the checker. `REVIEW-6.md` records what the last
adversarial pass found, including two published findings that were later withdrawn
and why.

## What is where

| Path | Role |
|---|---|
| `upstream/` | frozen canonical 1.8.0 (`server.py`, `compressor.py`, `start-proxy.ps1`, README, LICENSE). **Never executed.** `diff upstream/server.py proxy/server.py` shows every porting change. |
| `proxy/server.py` | ported HTTP proxy — routes, token accounting, proactive compression |
| `proxy/compressor.py` | ported summarizer — Mistral message shape, openai summarizer path |
| `hooks/start-proxy.ps1` | idempotent launcher (PID file + content-hash version + uv python) |
| `state/` | `proxy.pid`, `proxy.version` |

Logs go to `~/.vibe/logs/` (`rolling-context-debug.log`, `-proxy.log`, `-hook.log`).

## Wiring

Vibe honours **no** base-url environment variable — the whole of `vibe/core/`
has none. A `[[providers]]` entry is the only redirect surface. In `config.toml`:

```toml
[[providers]]
name = "rc-proxy"
api_base = "http://127.0.0.1:5590/v1"   # backend="mistral" requires <server>/v<digits>
api_key_env_var = "MISTRAL_API_KEY"
backend = "mistral"

[[models]]
alias = "mistral-medium-3.5-rc"
provider = "rc-proxy"
auto_compact_threshold = 0
```

`active_model = "mistral-medium-3.5-rc"` turns it on. The stock
`mistral-medium-3.5` entry is left in place — reverting is one word, and
`config.toml.pre-rollingcontext.bak` is the belt.

The API key is resolved env → **OS keyring** (`vibe_schema.py:93-100`), so the
proxy receives a real Bearer token with no env setup.

## Port notes — Vibe is not Claude Code

Five differences were load-bearing. Each was measured on live traffic, not inferred.

- **`system` is an IN-ARRAY message.** Anthropic carries it in a top-level
  `system` field, so upstream replaces `messages[0:cut]` freely. Vibe sends
  `['system','user','assistant','tool','tool']` with the prompt at index 0.
  Replacing from 0 deletes the system prompt — and the model keeps answering, so
  nothing looks broken. Every cut is floored at `_system_prefix_len()`.
- **Tool shape.** Anthropic `tool_use`/`tool_result` blocks inside content vs
  Mistral `tool_calls` on the assistant message plus a separate
  `{"role":"tool","tool_call_id","name","content"}`. This drives `_count_chars`,
  `_has_tool_use`, `_has_tool_result`, `_messages_to_text`, `_validate_tool_pairs`.
  Left unported, `_count_chars` reads tool-heavy conversations as nearly empty and
  **no compression ever fires** while the proxy reports healthy.
- **Hashing covers `tool_calls`.** Upstream hashes role+content only — safe when
  the call lives inside content, unsafe here, where assistant content is routinely
  `""`. Colliding hashes let `find_match()` splice a summary over the wrong messages.
- **Volatile tags.** Upstream stripped `system-reminder` etc. Those strings never
  occur in vibe traffic; the equivalents are the four in
  `vibe/core/utils/tags.py:8-13`. Unported, hashes never stabilise and every match
  misses.
- **Compression is PROACTIVE.** Upstream compresses for the *next* request, which
  loses a race against vibe's own compaction: `_loop.py:2219` sets
  `context_tokens` from `usage.prompt_tokens`, `middleware.py:104` compacts at
  `auto_compact_threshold`. Native compaction replaces the whole conversation with
  a lossy summary — the thing this proxy exists to prevent. The synchronous
  pre-forward block (ported from the GLM fork) plus `auto_compact_threshold = 0`
  closes it from both sides.

### Environment namespace

Every knob is `ROLLING_CONTEXT_VIBE_*`. Not tidiness — a **measured** collision.
A Claude-side install exports the unscoped names into the user environment:

```
ROLLING_CONTEXT_PORT=5588
ROLLING_CONTEXT_TRIGGER=250000
ROLLING_CONTEXT_TARGET=120000
ROLLING_CONTEXT_UPSTREAM=http://127.0.0.1:47821   <-- a chained proxy
```

This proxy booted with the Claude side's 250k/120k before the rename, and an
unscoped upstream would have sent Mistral summarization traffic — with a Mistral
bearer token — into the Anthropic chain. The PowerShell profile already carried a
note about the same class of bleed (`profile.ps1:51-54`, where 5588 was hijacking
the GLM head).

Port is **5590**: 5588 is the Claude side, 5589 is the GLM fork.

### Dropped from upstream

- `hooks.json` — vibe has no `SessionStart`; `HookType` is
  `POST_AGENT | PRE_TOOL | POST_TOOL` (`vibe/core/hooks/models.py:21-23`).
  A `pre_tool` starter would miss the first LLM turn, so the proxy is started by
  the `VRC` function in the PowerShell profile instead.
- The `settings.json` rewriting block in `start-proxy.ps1` — vibe is configured by
  `config.toml` and has no settings.json.
- `install.sh` / `uninstall.sh` / `docker-compose.e2e.yml`.
- **NATIVE summarizer mode** — it clones the session request to `/v1/messages` and
  parses Anthropic SSE. `SUMMARIZER_FORMAT` defaults to `openai`, which trips
  upstream's own rule and disables NATIVE with no logic change. Porting NATIVE
  against `/v1/chat/completions` is a real phase-2 win: Mistral does report cached
  tokens (measured `cached_tokens` 2080, and 6432 on a later run).

## Known-unverified

`[UNVERIFIED-STREAM]` — **resolved in review 6.** The streaming usage parser was
exercised against a rig that returns SSE `usage`: `prompt_tokens` is extracted
correctly and `prompt_tokens_details.cached_tokens` is correctly *not* summed. The
`chars // 4` fallback was separately re-derived and is proportional to the
**request** (`vibe-rc-server.py:1020`, assignment at `:1339`) — 40,000 chars → ~10,000
tokens. The original wording above was right: a wrong guess costs accuracy, not
correctness. A review-6 claim that it undercounted by ~31,000× was **withdrawn** as a
test-fixture artifact; see `REVIEW-6.md`.

## Uninstall

> **Do step 1 and step 2 together.** `mistral-medium-3.5` carries
> `auto_compact_threshold = 200000`, which is *below* the proxy's 220,000 trigger. If
> you switch the alias but leave the proxy running, vibe's native compaction wins and
> the proxy silently never fires. Killing the proxy is step 2 for that reason. The
> drift checker now resolves `active_model` and reports this as a failure — before
> review 6 it read a hardcoded alias and went green on exactly this state (R6-7).

Set `active_model = "mistral-medium-3.5"` (or restore
`config.toml.pre-rollingcontext.bak`), kill the PID in `state/proxy.pid`, delete
this directory, and remove `VRC` from the PowerShell profile.
