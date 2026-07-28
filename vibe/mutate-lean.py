#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Saimono / Nova-Violet Role
# SPDX-License-Identifier: AGPL-3.0-or-later OR EUPL-1.2

"""Mutation-test Compressor.lean, attributing CASCADES correctly.

The naive version of this script asked "which line did Lean report an error on".
That badly under-reports: when a theorem fails, Lean still declares it (backed by
`sorryAx`) and everything downstream keeps compiling, so a mutation that destroys
`monotone_shrink` via its dependency looks like `monotone_shrink` "surviving".

So instead: after each mutation, ask Lean `#print axioms T` for EVERY theorem. A
theorem that depends on `sorryAx` is not established, whether it failed itself or
inherited a broken lemma. That is the honest question - "is this theorem still
proved?" - and it is the one that decides load-bearing vs vacuous.
"""
import re
import subprocess
import sys
import os

LEAN = r"D:\Lean\proofs\Proofs\Compressor.lean"
HERE = os.path.dirname(os.path.abspath(__file__))
TMP = os.path.join(HERE, "mut.lean")
LEANBIN = os.path.expanduser(r"~\.elan\bin\lean.exe")
SRC = open(LEAN, encoding="utf-8").read()

MUTATIONS = [
    ("M01", "findKeepCore: drop the max(head,..) floor  [D3 half one]",
     "| some j => max (systemHead c) (min j (maxIdx c))",
     "| some j => min j (maxIdx c)"),
    ("M02", "findKeepCore: drop the min(..,maxIdx) pin  [retention floor]",
     "| none => max (systemHead c) (min i1 (maxIdx c))",
     "| none => max (systemHead c) i1"),
    ("M03", "badCut: allow a tail starting with a tool result",
     "| some m => m.role == Role.system || m.role == Role.tool",
     "| some m => m.role == Role.system"),
    ("M04", "badCut: allow a prefix ending on tool_calls",
     "| some m => m.hasToolCalls || m.role == Role.system",
     "| some m => m.role == Role.system"),
    ("M05", "safeCutAux: drop the clamp (return cut, not max cut floor)",
     "  | 0, cut => max cut floor\n  | fuel + 1, cut =>\n      if floor < cut \u2227 badCut c cut = true then\n        safeCutAux c floor fuel (cut - 1)\n      else\n        max cut floor",
     "  | 0, cut => cut\n  | fuel + 1, cut =>\n      if floor < cut \u2227 badCut c cut = true then\n        safeCutAux c floor fuel (cut - 1)\n      else\n        cut"),
    ("M06", "pinEligible: allow pinning tool results",
     "  m.role == Role.user && !m.hasToolCalls && !m.synthetic",
     "  (m.role == Role.user || m.role == Role.tool) && !m.synthetic"),
    ("M07", "pinEligible: drop the synthetic exclusion",
     "&& !m.hasToolCalls && !m.synthetic", "&& !m.hasToolCalls"),
    # --- review 5: the D-O / span-extraction family -------------------------
    ("M57", "pinEligible: re-admit assistant turns  [D-O, the self-pin]",
     "  m.role == Role.user && !m.hasToolCalls && !m.synthetic",
     "  (m.role == Role.user || m.role == Role.assistant) && !m.hasToolCalls && !m.synthetic"),
    ("M58", "pinExtract: retain the WHOLE message, not the authenticated span",
     "def pinExtract (m : Msg) : Msg := { m with chars := min m.pinChars m.chars }",
     "def pinExtract (m : Msg) : Msg := m"),
    ("M59", "pinExtract: drop the min, so retention can exceed the message",
     "def pinExtract (m : Msg) : Msg := { m with chars := min m.pinChars m.chars }",
     "def pinExtract (m : Msg) : Msg := { m with chars := m.pinChars }"),
    ("M60", "pinExtract: accumulate instead of replace  [breaks idempotence]",
     "def pinExtract (m : Msg) : Msg := { m with chars := min m.pinChars m.chars }",
     "def pinExtract (m : Msg) : Msg := { m with chars := m.pinChars + m.chars }"),
    ("M61", "pinExtract: clear `pinned`, so extraction un-pins what it carries",
     "def pinExtract (m : Msg) : Msg := { m with chars := min m.pinChars m.chars }",
     "def pinExtract (m : Msg) : Msg := "
     "{ m with chars := min m.pinChars m.chars, pinned := false }"),
    ("M62", "pinnedIn: stop extracting  [retention stops matching authentication]",
     "  (((c.drop lo).take (hi - lo)).filter effectivePinned).map pinExtract",
     "  ((c.drop lo).take (hi - lo)).filter effectivePinned"),
    ("M08", "rebuild: drop the pinned block  [hard memory removed]",
     "    ++ pinnedIn c (systemHead c) cut ++ c.drop cut", "    ++ c.drop cut"),
    ("M09", "stepE: delete the pinBudget branch",
     "  else if spanChars c (cutOf p c) \u2264 pinChars c (cutOf p c) then\n    .error .pinBudget\n", ""),
    ("M10", "stepE: delete the summaryTooLarge branch",
     "  else if spanChars c (cutOf p c)\n      \u2264 pinChars c (cutOf p c) + p.summaryChars c + p.ackChars then\n    .error .summaryTooLarge\n", ""),
    ("M11", "stepE: weaken the guard to `<`",
     "  if cutOf p c \u2264 startIdx c then", "  if cutOf p c < startIdx c then"),
    ("M12", "keepTarget: drop the division",
     "  countChars (body c) * keepNum / keepDen", "  countChars (body c) * keepNum"),
    ("M13", "maxIdx: stop pinning the last four messages",
     "def maxIdx (c : Conv) : Nat := c.length - 4",
     "def maxIdx (c : Conv) : Nat := c.length"),
    ("M14", "TRIGGER_TOKENS := vibe's default 200000  [ordering inversion]",
     "def TRIGGER_TOKENS : Nat := 220000", "def TRIGGER_TOKENS : Nat := 200000"),
    ("M15", "systemHead: always 0  [system prompt becomes compressible]",
     "  | m :: ms => if m.role = .system then systemHead ms + 1 else 0",
     "  | _ :: _ => 0"),
    ("M16", "fitCount: > becomes >=  [off-by-one in the backward walk]",
     "      if acc + m.chars > target then 0 else fitCount ms (acc + m.chars) target + 1",
     "      if acc + m.chars \u2265 target then 0 else fitCount ms (acc + m.chars) target + 1"),
    ("M17", "startIdx: stop skipping the previous [summary, ack] pair",
     "  systemHead c + (if hasSummary c then 2 else 0)", "  systemHead c"),
    ("M18", "body: budget over the whole array again  [D3 EXACTLY]",
     "def body (c : Conv) : Conv := c.drop (systemHead c)",
     "def body (c : Conv) : Conv := c"),
    ("M19", "rebuild: drop the system prefix from the output",
     "  c.take (systemHead c) ++ [summaryMsg p c, ackMsg p]",
     "  [summaryMsg p c, ackMsg p]"),
    ("M20", "rebuild: scan pins from startIdx instead of systemHead",
     "++ pinnedIn c (systemHead c) cut ++ c.drop cut",
     "++ pinnedIn c (startIdx c) cut ++ c.drop cut"),
    ("M21", "stepE: accept unconditionally  [all three guards removed]",
     "  if cutOf p c \u2264 startIdx c then\n    .error .nothingToCompress",
     "  if false then\n    .error .nothingToCompress"),
    ("M22", "safeCutAux: step down by 2 instead of 1",
     "        safeCutAux c floor fuel (cut - 1)", "        safeCutAux c floor fuel (cut - 2)"),
    ("M23", "run: zero round budget  [never iterates]",
     "def run (p : Policy) (c : Conv) : Conv := runAux (countChars c) p c",
     "def run (p : Policy) (c : Conv) : Conv := runAux 0 p c"),
    # --- the D-K / D-L tool-pair family --------------------------------------
    # RECONSTRUCTED in review 5. compressor-mutations.json recorded results for
    # L01-L10 and check-compressor-drift.py told anyone who asked to "run
    # mutate2.py" — a script that does not exist anywhere on this machine. So the
    # evidence for four [LOAD-BEARING] markers could not be reproduced from the
    # checked-in tooling, and regenerating the record with mutate-lean.py alone
    # silently downgraded those four theorems to "survived everything". An
    # instrument that cannot be re-run is not an instrument; these are restored
    # here so the record is reproducible from this file alone.
    ("L01", "validateToolPairsV4: reinstate the vf=0 early return  [shipped defect D-K]",
     "  let kept := (body.take vf).filter (rescuableFixed s) ++ body.drop vf\n"
     "  sys ++ dropOrphansAux (dropDangling kept) []",
     "  let kept := (body.take vf).filter (rescuableFixed s) ++ body.drop vf\n"
     "  if vf = 0 then sys ++ body else sys ++ dropOrphansAux (dropDangling kept) []"),
    ("L02", "dropDangling: accept every assistant (all-test -> true)",
     "        if m.callIds.all (fun cid => ms.any (fun r =>\n"
     "             r.role = Role.tool && r.resultId = some cid))\n"
     "        then m :: dropDangling ms\n        else dropDangling ms",
     "        m :: dropDangling ms"),
    ("L03", "dropDangling: drop tool messages too",
     "      else m :: dropDangling ms",
     "      else if m.role = Role.tool then dropDangling ms else m :: dropDangling ms"),
    ("L04", "danglingFree: made vacuously true",
     "def danglingFree (msgs : List SMsg) : Bool := danglingFreeAux msgs",
     "def danglingFree (_msgs : List SMsg) : Bool := true"),
    ("L05", "validateToolPairsShipped: made unconditional (i.e. already repaired)",
     "  if vf = 0 then sys ++ body\n"
     "  else sweep (sys ++ (body.take vf).filter (rescuableFixed s) ++ body.drop vf)",
     "  sweep (sys ++ (body.take vf).filter (rescuableFixed s) ++ body.drop vf)"),
    ("L06", "danglingFreeAux: drop the recursive conjunct",
     "          r.role = Role.tool && r.resultId = some cid)) && danglingFreeAux ms",
     "          r.role = Role.tool && r.resultId = some cid))"),
    ("L07", "danglingFreeAux: search the whole list, not the tail  [order-blind, D-L]",
     "        m.callIds.all (fun cid => ms.any (fun r =>\n"
     "          r.role = Role.tool && r.resultId = some cid)) && danglingFreeAux ms",
     "        m.callIds.all (fun cid => (m :: ms).any (fun r =>\n"
     "          r.role = Role.tool && r.resultId = some cid)) && danglingFreeAux ms"),
    ("L08", "validateToolPairsV4: remove the dropOrphansAux pass",
     "  sys ++ dropOrphansAux (dropDangling kept) []",
     "  sys ++ dropDangling kept"),
    ("L09", "dropOrphansAux: keep every tool message  [orphan filter off]",
     "            if known.contains rid then m :: dropOrphansAux ms known\n"
     "            else dropOrphansAux ms known",
     "            m :: dropOrphansAux ms known"),
    ("L10", "sysPrefixLen: always 0  [server-layer twin of the D3 mutation]",
     "  | m :: ms => if m.role = Role.system then sysPrefixLen ms + 1 else 0",
     "  | _ :: _ => 0"),
    ("M24", "pinnedIn: retain nothing",
     "  (((c.drop lo).take (hi - lo)).filter effectivePinned).map pinExtract",
     "  (((c.drop lo).take (hi - lo)).filter (fun _ => false)).map pinExtract"),
    ("M25", "effectivePinned: ignore the pin flag entirely",
     "def effectivePinned (m : Msg) : Bool := m.pinned && pinEligible m",
     "def effectivePinned (m : Msg) : Bool := false"),
    # M14 was too weak: 200000 is still below 245000, so it inverted nothing and
    # `rolling_precedes_native` survived it. These invert the orderings for real.
    ("M26", "TRIGGER_TOKENS := 250000  [ORDERING ACTUALLY INVERTED vs 245000]",
     "def TRIGGER_TOKENS : Nat := 220000", "def TRIGGER_TOKENS : Nat := 250000"),
    ("M27", "TARGET_TOKENS := 230000  [target above trigger: recompress forever]",
     "def TARGET_TOKENS : Nat := 120000", "def TARGET_TOKENS : Nat := 230000"),
    ("M28", "startIdx: subtract the summary pair instead of adding it [sign error]",
     "  systemHead c + (if hasSummary c then 2 else 0)",
     "  systemHead c - (if hasSummary c then 2 else 0)"),
    ("M29", "safeCutAux: clamp to floor+1  [off-by-one clamp, flips the guard]",
     "  | 0, cut => max cut floor\n  | fuel + 1, cut =>\n      if floor < cut ∧ badCut c cut = true then\n        safeCutAux c floor fuel (cut - 1)\n      else\n        max cut floor",
     "  | 0, cut => max cut (floor + 1)\n  | fuel + 1, cut =>\n      if floor < cut ∧ badCut c cut = true then\n        safeCutAux c floor fuel (cut - 1)\n      else\n        max cut (floor + 1)"),

    # --- sections 9-11: tag authentication, the sanitizer, the key chain ------
    # These cover the layers every defect of the last three rounds lived in and
    # that sections 1-8 cannot see.
    ("M30", "mintShipped: domain-separate it  [the D-C/D-D repair]",
     "def mintShipped (s : Secret) (_k : TagKind) (b : Body) : Tag :=\n  { secret := s, kind := none, body := b }",
     "def mintShipped (s : Secret) (_k : TagKind) (b : Body) : Tag :=\n  { secret := s, kind := some _k, body := b }"),
    ("M31", "firstTag: ignore the marker kind  [any tag satisfies any marker]",
     "  match t.tags.find? (fun p => p.1 == k) with",
     "  match t.tags.find? (fun _p => true) with"),
    ("M32", "canonBody: constant  [_strip_tags returns the same body for all texts]",
     "def canonBody (t : TaggedText) : Body := t.body",
     "def canonBody (_t : TaggedText) : Body := \"\""),
    ("M33", "verifyWith: accept whenever a tag is PRESENT  [MAC not checked]",
     "  | some tg => tg == mint s k (canonBody t)\n  | none => false",
     "  | some _tg => true\n  | none => false"),
    ("M34", "rescuableShipped: gate on role and tool-freedom  [the D-E repair]",
     "def rescuableShipped (s : Secret) (m : SMsg) : Bool :=\n  sEffectivePinned s m || sIsSynthetic s m",
     "def rescuableShipped (s : Secret) (m : SMsg) : Bool :=\n  rescuableFixed s m"),
    ("M35", "sIsSynthetic: drop the ack-literal branch",
     "  verifyShipped s TagKind.summary m.text || (canonBody m.text == ackBody)",
     "  verifyShipped s TagKind.summary m.text"),
    ("M36", "validateToolPairsFixed: drop the dropOrphansAux pass",
     "  sys ++ dropOrphansAux kept []", "  sys ++ kept"),
    ("M37", "dropOrphansAux: keep orphaned tool messages",
     "        | some rid =>\n            if known.contains rid then m :: dropOrphansAux ms known\n            else dropOrphansAux ms known\n        | none => dropOrphansAux ms known",
     "        | some _rid => m :: dropOrphansAux ms known\n        | none => m :: dropOrphansAux ms known"),
    ("M38", "findMatchGo: prefer the LAST occurrence, not the first",
     "      if occursAt chain (h :: t) then some (n + chain.length)\n      else findMatchGo (n + 1) chain t",
     "      match findMatchGo (n + 1) chain t with\n      | some e => some e\n      | none => if occursAt chain (h :: t) then some (n + chain.length) else none"),
    ("M39", "findMatchEnd: drop the empty-chain guard  [`if not oh` removed]",
     "  if chain.isEmpty then none else findMatchGo 0 chain hs",
     "  findMatchGo 0 chain hs"),
    ("M40", "chainStartWalk: never walk  [bare `start = 2`, i.e. defect D-A]",
     "  | i, m :: ms => if sEffectivePinned s m then chainStartWalk s (i + 1) ms else i",
     "  | i, _ :: _ => i"),
    ("M41", "chainStart: start the chain at 0  [previous summary pair not skipped]",
     "  chainStartWalk s 2 (summarized.drop 2)", "  chainStartWalk s 0 summarized"),
    ("M42", "rescuableFixed: ungate the role/tool test  [back to rescuableShipped]",
     "  (sEffectivePinned s m || sIsSynthetic s m)\n    && (m.role == Role.user || m.role == Role.assistant)\n    && m.callIds.isEmpty && m.resultId.isNone",
     "  (sEffectivePinned s m || sIsSynthetic s m)"),
    ("M43", "sPinEligible: allow pinning tool results  [server-layer twin of M06]",
     "  (m.role == Role.user || m.role == Role.assistant) && !sHasToolUse m && !sIsSynthetic s m",
     "  !sIsSynthetic s m"),
    ("M44", "orphanFreeAux: treat an id-less tool message as legal",
     "        | some rid => known.contains rid && orphanFreeAux ms known\n        | none => false",
     "        | some rid => known.contains rid && orphanFreeAux ms known\n        | none => orphanFreeAux ms known"),
    ("M45", "validFromAux: stop accumulating ids across dropped messages",
     "        validFromAux ms (i + 1) (known ++ m.callIds) vf",
     "        validFromAux ms (i + 1) m.callIds vf"),
    ("M46", "sysPrefixLen: always 0  [system prefix not recognised, server layer]",
     "  | m :: ms => if m.role = Role.system then sysPrefixLen ms + 1 else 0\n\n/-- The `valid_from` scan",
     "  | _ :: _ => 0\n\n/-- The `valid_from` scan"),
    # --- review 6: the drop-invariant / reachability family -----------------
    # These exist because the review-6 theorems were added with NO mutation
    # covering them, and an untested theorem is an unaudited claim. Each names
    # the review-6 theorem it is meant to kill; whether it actually does is
    # measured, not assumed.
    ("M63", "maxIdx: unpin the last four messages  [kills the reachability floor]",
     "def maxIdx (c : Conv) : Nat := c.length - 4",
     "def maxIdx (c : Conv) : Nat := c.length"),
    ("M64", "stepE: accept when the span merely EQUALS pins+summary+ack "
            "[kills the strict drop: forwarded size could tie, not shrink]",
     "  else if spanChars c (cutOf p c)\n      ≤ pinChars c (cutOf p c) + p.summaryChars c + p.ackChars then",
     "  else if spanChars c (cutOf p c)\n      < pinChars c (cutOf p c) + p.summaryChars c + p.ackChars then"),
    ("M65", "rebuild: drop the pinned block from the replacement "
            "[retention gone; the shrink theorems must not depend on it]",
     "  c.take (systemHead c) ++ [summaryMsg p c, ackMsg p]\n    ++ pinnedIn c (systemHead c) cut ++ c.drop cut",
     "  c.take (systemHead c) ++ [summaryMsg p c, ackMsg p] ++ c.drop cut"),
    ("M66", "countChars: ignore the tail  [breaks the size algebra outright]",
     "def countChars (c : Conv) : Nat := (c.map (·.chars)).sum",
     "def countChars (c : Conv) : Nat := 0"),
]

# `strongRec` is `private`, so `#print axioms Compressor.strongRec` cannot resolve
# it. It is core-only strong induction with no compressor content whatsoever -
# the same eliminator Nat.strongRecOn provides. Exempt, with the reason recorded
# rather than silently skipped.
EXEMPT = {"strongRec": "private; core-only strong induction, no compressor content"}


def theorem_names(src):
    """Real theorem declarations, in order. Doc-comment prose is excluded by
    requiring the name to be followed by a binder, `:` or `{`."""
    out = []
    for line in src.split("\n"):
        m = re.match(r"^(?:private )?theorem (\w+)\s*[\s:({\[]", line)
        if m:
            out.append(m.group(1))
    return out


def run_lean(text, names):
    probes = "\n".join(f"#print axioms Compressor.{n}" for n in names)
    open(TMP, "w", encoding="utf-8").write(text + "\n\n" + probes + "\n")
    r = subprocess.run([LEANBIN, TMP], capture_output=True, text=True,
                       encoding="utf-8", errors="replace")
    blob = r.stdout + r.stderr
    broken, unknown = set(), set()
    for n in names:
        # Lean prints one of two forms; "no axioms" is the CLEANEST result and an
        # earlier version of this script scored it as failure.
        if re.search(rf"'Compressor\.{re.escape(n)}' does not depend on any axioms", blob):
            continue
        m = re.search(rf"'Compressor\.{re.escape(n)}' depends on axioms: \[([^\]]*)\]", blob)
        if m:
            if "sorryAx" in m.group(1):
                broken.add(n)
        elif re.search(rf"[Uu]nknown (?:constant|identifier) `?Compressor\.{re.escape(n)}", blob):
            unknown.add(n)   # not a real declaration (doc-comment false positive)
        else:
            broken.add(n)
    return r.returncode, broken, unknown


def main():
    names = [n for n in theorem_names(SRC) if n not in EXEMPT]
    rc, broken, unknown = run_lean(SRC, names)
    names = [n for n in names if n not in unknown]
    if unknown:
        print(f"(dropped {len(unknown)} doc-comment false positive(s): "
              f"{', '.join(sorted(unknown))})")
    rc, broken, _ = run_lean(SRC, names)
    if rc != 0 or broken:
        print(f"BASELINE NOT CLEAN: rc={rc}, unproved={sorted(broken)[:6]}")
        return 2
    print(f"baseline: {len(names)} theorems, all proved, 0 depend on sorryAx\n")

    killed = {n: [] for n in names}
    for mid, desc, old, new in MUTATIONS:
        if old not in SRC:
            print(f"{mid}  !! PATTERN NOT FOUND (mutation never applied): {desc}")
            continue
        _, brk, _ = run_lean(SRC.replace(old, new, 1), names)
        for n in brk:
            killed[n].append(mid)
        tag = "NO EFFECT" if not brk else f"breaks {len(brk):>2}"
        print(f"{mid}  {tag:<10}  {desc}")
    open(TMP, "w", encoding="utf-8").write(SRC)

    corpus = [n for n in names if n.startswith("case_")]
    core = [n for n in names if not n.startswith("case_")]
    print("\n" + "=" * 76)
    print("PER-THEOREM (core theorems; corpus summarised at the end)")
    print("=" * 76)
    surv = []
    for n in core:
        if killed[n]:
            print(f"  LOAD-BEARING  {n:<30} {','.join(killed[n])}")
        else:
            surv.append(n)
    print()
    for n in surv:
        print(f"  SURVIVED ALL  {n}")
    ck = sum(1 for n in corpus if killed[n])
    print(f"\ncorpus: {ck}/{len(corpus)} killed by >=1 mutation")
    print(f"core:   {len(core) - len(surv)}/{len(core)} load-bearing, "
          f"{len(surv)} survived every mutation")

    import json
    out = {
        "_comment": [
            "MEASURED, not asserted. Generated by mutate-lean.py. For each theorem in",
            "Compressor.lean, the mutations of the model that stop it being proved,",
            "determined by `#print axioms` (so a theorem broken through a dependency",
            "is counted, not silently scored as surviving).",
            "",
            "check-compressor-drift.py phase 5 enforces two things against this file:",
            "  - no theorem exists in the Lean file that was never mutation-tested",
            "    (a new theorem is unaudited until it appears here);",
            "  - no theorem marked [LOAD-BEARING] in its doc comment actually",
            "    survived every mutation. That marker is a claim, and this is the",
            "    evidence for it.",
            "Regenerate with: python mutate-lean.py  (~5 min, one full Lean compile",
            "per mutation).",
        ],
        "exempt": EXEMPT,
        "mutations": {mid: desc for mid, desc, _o, _n in MUTATIONS},
        "killed_by": {n: killed[n] for n in names},
    }
    dest = os.path.join(HERE, "compressor-mutations.json")
    with open(dest, "w", encoding="utf-8") as fh:
        json.dump(out, fh, indent=1)
    print(f"\nwrote {dest}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
