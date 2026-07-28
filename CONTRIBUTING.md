# Contributing

This project has an unusual property for a piece of proxy software: parts of it are
*proved*, not merely tested. That changes what contributing looks like, so this
document is specific rather than generic.

## The short version

- Bug reports and questions: open an issue. You do not need to have a fix.
- Changes to the compression policy: read *The proof obligation* below first.
- Changes to anything else: a normal pull request is fine.
- Security problems: **do not open an issue** — see [SECURITY.md](SECURITY.md).

## What is most useful

**Reports of it getting something wrong.** A conversation where compression dropped
something it should have kept is worth more than a feature request. Include the
message sequence if you can share it, and the thresholds you were running.

**Ports and adapters.** The proxy already targets Claude Code and the Mistral Vibe
CLI. Anything speaking a comparable API is a candidate.

**Proof work.** Thirteen theorems currently survive all 66 injected mutations, meaning
they are true but constrain nothing. Turning one of those into a load-bearing theorem —
or showing why it cannot be — is a genuinely valuable contribution.

**Documentation.** If something here was hard to understand, that is a defect in the
writing, and saying so is a contribution.

## The proof obligation

`vibe/lean/` formalizes the compression policy. If your change alters how messages are
selected, cut, merged, or pinned, the model must change with it.

A pull request that changes the policy but not the proofs will be asked one question:
*which theorem should now be false?* There are three honest answers, and all three are
acceptable:

1. **None** — the change is outside the model's scope. Say which part, and why.
2. **This one, and here is the updated proof.** Ideal.
3. **I do not know how to update the proof.** Also fine — open the PR and say so. We
   would rather work it out together than have you abandon the change.

What is not acceptable is deleting or weakening a theorem to make a build pass. If a
proof fails, the proof is usually right.

### Running the proofs

```bash
cd vibe/lean
lake exe cache get     # prebuilt mathlib — minutes instead of hours
lake build             # must exit 0
```

CI runs this on every push, and separately asserts that no `sorry` survives — `lake
build` alone reports `sorry` as a warning and would stay green on an incomplete proof.

### Running the drift gate

```bash
cd vibe
uv run --no-project python check-compressor-drift.py    # must print CLEAN
```

**This one is local-only, on purpose.** Phase 4 of 7 reads the live
`~/.vibe/config.toml` of the machine it runs on, to confirm the *installed* thresholds
are correctly ordered. CI has no such install. We could write a fixture config to make
it pass in CI, and that is precisely why we do not: it would then be checking a file we
generated in the workflow and would report green no matter what a real installation
contained. A green tick that cannot fail is worse than no tick. Run it locally before
proposing a release.

## Pull requests

- Branch from `master`.
- Say what changed and why. If it fixes an issue, link it.
- Commit messages here are long by convention — they explain what a file is for and
  what a change does, because the repository is meant to be readable by someone
  arriving a year later with no context. Match that if you can; we will not reject a
  PR over commit prose.
- Keep unrelated changes in separate PRs.

**Do not modify `proxy/`, `hooks/`, `tests/`, or the installers unless your change is
specifically about them.** Those files are upstream's, under MIT, and are deliberately
kept byte-identical so that changes flow cleanly in both directions. Work belonging to
this project goes in `vibe/`. See [NOTICE](NOTICE).

## Licensing of contributions

Contributions to original work in this repository are accepted under
**AGPL-3.0-or-later OR EUPL-1.2**, the same dual licence the project itself carries.
Contributions to upstream-derived files under `proxy/`, `hooks/`, `tests/` and the
installers remain **MIT**, matching those files.

By opening a pull request you confirm you have the right to contribute the code under
those terms. There is no CLA — we are not asking you to assign copyright, only to
confirm you can licence what you wrote.

## A note on tone

This project documents its own mistakes in its commit history, including retractions
where an earlier claim turned out to be wrong. That is deliberate. You will not be
made to feel foolish for a bad patch, a misunderstanding, or a question that turns out
to have an obvious answer. Being wrong in the open is how the rest of it got built.
