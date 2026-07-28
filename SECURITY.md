# Security Policy

This project sits in the path of your API traffic. It reads and rewrites the message
history of your AI sessions before forwarding them upstream. That places it in a
position of real trust, and this document exists so that a person who finds a flaw
knows exactly where to send it.

## Reporting a vulnerability

**Please do not open a public issue for a security problem.**

Use GitHub's private reporting: **Security → Report a vulnerability** on this
repository. It is the fastest route and it keeps the details out of public view until
there is something to upgrade to.

If that is unavailable to you, open an issue containing only *"security report, please
provide a contact route"* — with no technical detail — and we will respond with one.

### What helps

- What an attacker gains, concretely.
- The smallest reproduction you can manage — a request, a config, a message sequence.
- Which component: the proxy (`proxy/`, `vibe/vibe-rc-server.py`), the compressor
  (`compressor.py`), the installer, or the hooks.
- Your view of severity, and why. Disagreeing with our assessment is useful.

### What to expect

- Acknowledgement within **72 hours**.
- An initial assessment — including *"this is not a vulnerability, and here is why"* —
  within **7 days**. A clear no is a real answer and you will get one rather than
  silence.
- Credit in the fix, unless you would rather not be named.

This is a small non-profit project maintained by volunteers. We cannot promise the
response times of a funded security team, and we would rather state that than let you
discover it while waiting.

## Scope

**In scope**

- The proxy: request/response handling, header and auth forwarding, endpoint routing.
- The compressor: anything where crafted message content changes what is retained,
  dropped, or leaked across the summary boundary.
- The pin mechanism, including the HMAC construction in `state/pin-secret`.
- Installers and hooks: privilege, path handling, and what they write where.

**Out of scope**

- Vulnerabilities in the upstream model providers themselves.
- Findings that require an attacker who already has local read access to the user's
  home directory. See the known limitation below — we would still like to hear about
  it, but we will likely already agree with you.

## Known limitations, stated up front

We would rather you learn these here than report them as discoveries.

**`state/pin-secret` is mode 0644.** The 256-bit HMAC key that authenticates pin
markers is readable by any process running as the user. Any local process able to read
it can forge a pin marker. The mitigation is that it is per-install and never
transmitted; the limitation is real and documented rather than hidden.

**The proxy trusts its configured upstream.** It does not pin certificates beyond
the platform trust store, and a `base_url` pointing somewhere hostile will receive
your traffic. Point it only at endpoints you trust.

**Compression is lossy by construction.** Messages outside the retained window are
replaced by a model-written summary. What survives verbatim is guaranteed for
*pinned* messages — proved, see `pinned_never_cut` — and for the recent window. Nothing
is promised about the fidelity of the summary itself, and no proof in this repository
claims otherwise.

## Supported versions

The `master` branch is the supported version. This project does not currently backport
fixes to tags. If you are running a fork or a pinned revision, please confirm the issue
against current `master` before reporting.
