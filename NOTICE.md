# NOTICE — claude-rolling-context-Lean-4-

This file maps the licence that applies to each part of this repository and credits the
upstream work it stands on. Read it before copying anything: **which licence applies
depends on which files you take.**

> **This repository is a FORK, not an original work.** That distinction governs the
> licensing below. Nova-Violet Role dual-licenses its *original* projects under
> AGPL-3.0-or-later OR EUPL-1.2. A fork is not an original project, so that dual grant
> is applied **only to the work we actually wrote** — not to the repository as a whole,
> and never retroactively to someone else's code.

---

## §A — THE LICENCE MAP (which path is under which licence)

Licence applies **by provenance, never by directory convenience**.

### 1. MIT — the upstream project, and therefore the repository root

```
proxy/                      compressor.py, server.py, endpoints.py
hooks/                      start-proxy.ps1, start-proxy.sh, hooks.json
tests/                      mock_endpoint.py, test_custom_endpoint.py
install.ps1  install.sh  uninstall.ps1  uninstall.sh
.claude-plugin/plugin.json
docker-compose.e2e.yml
vibe/vendored-upstream/     preserved copy of the exact fork point
README.md                   upstream's document, extended by us
```

Copyright (c) 2026 **NodeNestor**. Licensed under the MIT Licence — the verbatim text is
at **`LICENSE`** in the repository root, unchanged.

`LICENSE` remains MIT deliberately. It is the licence of the project this repository
forked from, and the root licence file of a fork should say what the fork actually is.
GitHub's detected licence for this repository is therefore MIT, which is correct.

**These files were not relicensed.** MIT permits sublicensing, so placing them under the
AGPL would have been lawful. We chose not to. They stay MIT with their notice intact so
that anyone — including upstream — can take them back on the terms they were given.

### 2. AGPL-3.0-or-later OR EUPL-1.2 — our original work

```
vibe/                       the Mistral Vibe CLI port
  vibe-rc-server.py           the proxy
  compressor.py               the compression engine
  check-compressor-drift.py   the ship gate
  mutate-lean.py              the mutation harness
  compressor-cases.json       the fixed corpus
  compressor-mutations.json   the mutation catalogue
  hooks/start-proxy.ps1       the launcher
  README.md  REVIEW-6.md      the port's own documentation
vibe/lean/                  the Lean 4 formalization (157 theorems)
.github/workflows/          CI
NOTICE.md  CITATION.cff  SECURITY.md  CONTRIBUTING.md  CODE_OF_CONDUCT.md
```

Copyright (c) 2026 **Saimono / Nova-Violet Role**.

Every original source file carries the dual SPDX tag:

<!-- REUSE-IgnoreStart -->
```
SPDX-License-Identifier: AGPL-3.0-or-later OR EUPL-1.2
```
<!-- REUSE-IgnoreEnd -->

You may take this work under **either** licence, at your option. The verbatim texts are
at **`LICENSE-AGPL-3.0-or-later`** and **`LICENSE-EUPL-1.2`**; machine-readable copies
live under **`LICENSES/`** per the [REUSE](https://reuse.software) convention.

**Why AGPL.** This is a proxy. It sits in the request path and can be run as a hosted
service without ever distributing a binary — the precise gap ordinary GPL leaves open
and the AGPL closes.

**Why also EUPL.** The EUPL is the only copyleft licence with official legal standing in
all 24 EU languages, and its Article 5 lists AGPL-3.0 among the compatible licences.
Several European public bodies may adopt EUPL-licensed work but cannot adopt GPL-family
work under procurement rules. Offering both removes that barrier without weakening the
copyleft. For a non-profit that wants public institutions to be able to say yes, that is
not a technicality.

---

## §B — A CORRECTION ON THE RECORD

Files under `vibe/lean/Proofs/` previously carried **"Apache 2.0"** headers. That was
inherited boilerplate from the Mathlib file template. It reflected no decision by anyone
here, and it granted terms this repository did not offer.

The headers now carry the dual SPDX tag from §A.2.

This is recorded rather than fixed silently because a file asserting a licence its
repository does not grant is exactly the ambiguity that stops an institution from
adopting a project — and someone may have read the old header and relied on it.

---

## §C — CREDITS

**NodeNestor** — the upstream *rolling-context* proxy for Claude Code, from which this
repository is forked. The compression architecture, the plugin packaging and the
installer design are theirs. `vibe/vendored-upstream/` preserves the exact revision the
port diverged from, so their work and ours can be told apart by anyone with `diff`.

**Lean 4 and mathlib** (leanprover-community) — the proof assistant and library the
formalization is built on. Used as a dependency under their own terms, not vendored
here; see `vibe/lean/lakefile.toml` for the pinned revision.

---

## §D — IF YOU ARE UNSURE

**Taking only §A.1 files** — the MIT terms alone apply.

**Taking §A.2 files, or combining both** — the result must satisfy the AGPL (or the
EUPL). MIT-licensed code can be combined into a copyleft work; the reverse is not true.

**Anything else** — open an issue. We would rather answer than have you guess.
