#!/usr/bin/env python3
"""Phase D mechanical post-rebase lints for Lean rounds.

Runs after lake build / check-axioms / audit / axiom-purity, before merge.
Three checks on declarations introduced in this round
(`<base-branch>..HEAD` under `lean4/BEDC/`):

  1. Mechanical-arity suffix on a new declaration name
     (`_two`, `_three`, `_four`, `_five`, `_six`, `_*_step`,
     `_*_witness_chain`).
  2. Parameter-echo schema: signature binds a hypothesis
     `(name : forall … hsame …)` — i.e. quantifies over an hsame law as
     input rather than proving anything specific about a concrete BEDC
     kernel object.
  3. BHist-anchor: every new theorem under `BEDC.Derived.*` must mention
     at least one concrete BEDC kernel symbol in its signature
     (BHist / BMark / hsame / ProbeBundle / SigRel / NameCert / Pkg /
     etc).

Used by `codex_formalize.py::run_phase_d_lints` via subprocess. Splitting
the lint into its own script means the regex set can be tightened
without restarting the pipeline — the next call (next round's pre-merge
gate) picks up the change.

Usage:

    python3 lean4/scripts/phase_d_lint.py \
        --worktree /path/to/formalize_target_wabc1234 \
        --base-branch codex-auto-dev

Exit code 0 = clean. Exit code 1 = at least one violation; details on
stdout suitable for inclusion in a codex recovery prompt.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path

DECL_RE = re.compile(
    r"^\s*(theorem|lemma|def|inductive|structure|class)\s+(\w+)"
)
MECHANICAL_ARITY_RE = re.compile(
    r"_(two|three|four|five|six)(?:_step)?(?:_witness_chain)?\b"
)
PARAMETER_ECHO_BIND_RE = re.compile(
    r"\(\s*(\w+)\s*:\s*(?:∀|forall)\b[^)]*hsame\b", re.DOTALL
)
PARAMETER_ECHO_CONCL_RE = re.compile(
    r"(?:∀|forall)\b[^,]*,[^.]*hsame\b", re.DOTALL
)
BY_DECIDE_RE = re.compile(r"\bby\s+decide\b")
LIST_RANGE_NUM_RE = re.compile(r"\bList\.range\s*\(?\s*([0-9]+)\b")
FOLDL_ACC_APPEND_RE = re.compile(
    r"(?:\bfoldl\b[\s\S]{0,2000}\bacc\s*\+\+|\bacc\s*\+\+[\s\S]{0,2000}\bfoldl\b)"
)
PUBLIC_THEOREM_HEADER_RE = re.compile(
    r"^\s*(?:@\[[^\]]+\]\s*)*(?:(?:noncomputable|unsafe)\s+)*"
    r"(?:protected\s+)?(?:theorem|lemma)\s+([A-Za-z_][\w']*)\b"
)
PRIVATE_THEOREM_HEADER_RE = re.compile(
    r"^\s*(?:@\[[^\]]+\]\s*)*private\s+(?:(?:noncomputable|unsafe)\s+)*"
    r"(?:protected\s+)?(?:theorem|lemma)\b"
)
LEAN_COMMAND_START_RE = re.compile(
    r"^\s*(?:@\[[^\]]+\]\s*)*"
    r"(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+|partial\s+)?"
    r"(?:namespace|section|end|theorem|lemma|def|inductive|structure|class|"
    r"instance|abbrev|opaque|example|mutual|open|variable|universe)\b"
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*)\b")
SECTION_RE = re.compile(r"^\s*section(?:\s+[A-Za-z_][\w']*)?\s*$")
END_RE = re.compile(r"^\s*end(?:\s+[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*)?\s*$")
THIN_WRAPPER_BODY_RE = re.compile(
    r"^(?:by\s+exact\s+|exact\s+)?[A-Za-z_][\w'.]*(?:\s+[^:=;|{}]+)?$"
)
PROBE_TIMEOUT_SECONDS = 90

# Value-instance saturation: a round satisfies a classical theorem target by
# adding several sibling point instances (e.g. `WolstenholmeBinomialNat 5/7/11/13
# := by decide`) instead of proving one parameterised ∀-theorem. The instances
# differ only by an embedded numeric value and carry a trivial proof, so the
# shared theorem has no mathematical compression — only N closed computations.
# Distinct from MECHANICAL_ARITY_RE (which is name-local on _two…_six); this
# detects the higher-level family across a round's added declarations.
VALUE_WORDS = (
    "two|three|four|five|six|seven|eight|nine|ten|eleven|twelve|thirteen|"
    "fourteen|fifteen|sixteen|seventeen|eighteen|nineteen|twenty|"
    "thirty|forty|fifty|sixty|seventy|eighty|ninety|hundred|thousand"
)
VALUE_SUFFIX_RE = re.compile(
    rf"_(?:[0-9]+|(?:{VALUE_WORDS})(?:[A-Z][A-Za-z0-9]*)*)\b"
)
VALUE_NAT_LITERAL_RE = re.compile(r"(?<![A-Za-z0-9_])([2-9]|[1-9][0-9]+)(?![A-Za-z0-9_])")
# Base/step/recursion vocabulary is legitimate (defining a sequence); never a
# value-saturation token. `_zero`/`_one` are deliberately excluded above.
VALUE_BASE_STEP_RE = re.compile(
    r"_(zero|one|succ|step|rec|recurrence|induction|unfold|closed_form|formula|base)\b"
)
# A bound mathematical parameter in the signature means the statement is already
# parameterised (general), not a closed value instance — exempt.
VALUE_BOUND_VAR_RE = re.compile(
    r"\(\s*\w+\s*:\s*Nat\s*\)|[({]\s*\w+\s*:\s*BHist\s*[)}]|"
    r"[({]\s*\w+\s*:\s*NatPrime\b|\(\s*prime\s*:\s*NatPrime\b|(?:∀|forall)\b"
)
# Concrete finite-field carrier facts are often legitimate interface smoke tests;
# `zmodInvTotal`-style general theorems (parameterised over ZMod p) must remain
# untouched — exempt any signature touching the ZMod surface.
VALUE_ZMOD_EXEMPT_RE = re.compile(r"\bZMod\b|\bzmodEq\b|\bzmod\w*\b|\bnatToUnary\b")
# A trivial closed proof: the instance is decided/reflexive, no real reasoning.
VALUE_TRIVIAL_PROOF_RE = re.compile(
    r":=\s*by\s+(?:native_decide|decide)\b"
    r"|:=\s*(?:native_decide|decide|rfl)\b"
    r"|:=\s*by\s*\n\s*(?:native_decide|decide|rfl)\b"
)
VALUE_HEAD_RE = re.compile(r"[A-Za-z_][\w'.]*")
VALUE_INSTANCE_THRESHOLD = 4


def _strip_hsame_tokens(text: str) -> str:
    """Drop `hsame` and the bare `BHist` type token so the residual anchor
    scan only fires on substantive constructors (Empty/e0/e1/Cont/NameCert/…)."""
    text = re.sub(r"\bhsame\b", "", text)
    text = re.sub(r"\bBHist\b", "", text)
    return text


def _extract_conclusion(sig: str) -> str:
    """Return the part of `sig` after the last top-level `:` (the goal type)."""
    depth = 0
    last_colon = -1
    for i, ch in enumerate(sig):
        if ch in "({[":
            depth += 1
        elif ch in ")}]":
            depth -= 1
        elif ch == ":" and depth == 0:
            last_colon = i
    return sig[last_colon + 1:] if last_colon >= 0 else sig
BHIST_CONSTRUCTOR_RE = re.compile(
    r"\b("
    # FKernel primitive constructors (the original kernel layer)
    r"BHist|BMark|Empty|e0|e1|cons|append|sameSig|"
    r"ProbeBundle|SigRel|InGap|NameCert|SemanticNameCert|Pkg|hsame|msame|"
    r"Cont|Ext|InBundle|SameSig|UnaryHistory|StageInterface|"
    r"SealEvent|SealInterface|AskEvent|AskPolicy|BundleAskPolicy|"
    r"DescentCertificate|StableTransformation|ThreadFamily|"
    r"bundleAppend|bundleLength|bwordLength|"
    # BEDC-defined typeclasses that derived chapters routinely instance —
    # mentioning these counts as anchoring because the typeclass itself
    # is BHist-grounded (BHistCarrier requires toEventFlow into EventFlow,
    # ChapterTasteGate requires round_trip + layer_separation, etc.)
    r"BHistCarrier|ChapterTasteGate|FieldFaithful|"
    # Any \w+Up identifier — derived chapter carriers and their projections.
    # By BEDC convention every chapter under BEDC/Derived/ exposes <Name>Up
    # as its carrier. A theorem/instance mentioning any <X>Up name is
    # transitively anchored through that chapter's BHist carrier definition.
    r"\w+Up"
    r")\b"
)
DERIVED_PATH_PREFIX = "lean4/BEDC/Derived"
SIGNATURE_BLOCK_LIMIT = 40


def _strip_lean_comments(text: str) -> str:
    out: list[str] = []
    i = 0
    block_depth = 0
    while i < len(text):
        if block_depth:
            if text.startswith("/-", i):
                block_depth += 1
                i += 2
            elif text.startswith("-/", i):
                block_depth -= 1
                i += 2
            else:
                if text[i] == "\n":
                    out.append("\n")
                i += 1
            continue
        if text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                i += 1
            continue
        if text.startswith("/-", i):
            block_depth = 1
            i += 2
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def _is_public_thin_wrapper_source(block: str) -> bool:
    cleaned = _strip_lean_comments(block)
    lines = cleaned.splitlines()
    saw_public_header = False
    for line in lines:
        if not line.strip():
            continue
        if PRIVATE_THEOREM_HEADER_RE.match(line):
            return False
        if PUBLIC_THEOREM_HEADER_RE.match(line):
            saw_public_header = True
            break
    if not saw_public_header or ":=" not in cleaned:
        return False

    body = cleaned.split(":=", 1)[1]
    body_lines = [line.strip() for line in body.splitlines() if line.strip()]
    if not body_lines or len(body_lines) > 2:
        return False

    flat = " ".join(body_lines)
    flat = re.sub(r"\s+", " ", flat).strip()
    if flat.startswith("by ") and not re.match(r"^by\s+exact\s+", flat):
        return False
    if re.search(r"(?:<;>|=>|[;|{}])", flat):
        return False
    if re.search(
        r"\b(?:apply|constructor|cases|induction|have|simpa|simp|rw|"
        r"unfold|change|calc|show|refine|first|repeat)\b",
        flat,
    ):
        return False
    return bool(THIN_WRAPPER_BODY_RE.fullmatch(flat))


def _added_line_numbers_by_file(worktree: Path, base_branch: str) -> dict[str, set[int]]:
    res = subprocess.run(
        [
            "git", "diff", "--unified=0", "--no-color",
            f"{base_branch}..HEAD", "--", "lean4/BEDC/",
        ],
        cwd=worktree, capture_output=True, text=True, check=False,
    )
    if res.returncode != 0:
        return {}
    added: dict[str, set[int]] = {}
    current_file: str | None = None
    new_line: int | None = None
    for raw in res.stdout.splitlines():
        if raw.startswith("+++ b/"):
            current_file = raw[len("+++ b/"):]
            new_line = None
            continue
        if raw.startswith("@@"):
            m = re.search(r"\+(\d+)(?:,(\d+))?", raw)
            new_line = int(m.group(1)) if m else None
            continue
        if current_file is None or new_line is None:
            continue
        if raw.startswith("+") and not raw.startswith("+++"):
            added.setdefault(current_file, set()).add(new_line)
            new_line += 1
        elif raw.startswith("-") and not raw.startswith("---"):
            continue
        elif raw.startswith(" "):
            new_line += 1
    return added


def _lean_module_from_rel_path(rel_path: str) -> str:
    path = rel_path
    if path.startswith("lean4/"):
        path = path[len("lean4/"):]
    if path.endswith(".lean"):
        path = path[:-len(".lean")]
    return path.replace("/", ".")


def _parse_public_theorem_blocks(text: str) -> list[tuple[str, str, int]]:
    original_lines = text.splitlines()
    clean_lines = _strip_lean_comments(text).splitlines()
    scopes: list[tuple[str, str]] = []
    blocks: list[tuple[str, str, int]] = []
    i = 0
    while i < len(clean_lines):
        line = clean_lines[i]
        ns_match = NAMESPACE_RE.match(line)
        if ns_match:
            scopes.append(("namespace", ns_match.group(1)))
            i += 1
            continue
        if SECTION_RE.match(line):
            scopes.append(("section", ""))
            i += 1
            continue
        if END_RE.match(line):
            if scopes:
                scopes.pop()
            i += 1
            continue

        private_header = PRIVATE_THEOREM_HEADER_RE.match(line)
        public_header = PUBLIC_THEOREM_HEADER_RE.match(line)
        if private_header or public_header:
            start = i
            j = i + 1
            while j < len(clean_lines):
                if LEAN_COMMAND_START_RE.match(clean_lines[j]):
                    break
                j += 1
            if public_header:
                namespaces = [name for kind, name in scopes if kind == "namespace"]
                leaf = public_header.group(1)
                qualified = ".".join([*namespaces, leaf]) if namespaces else leaf
                block = "\n".join(original_lines[start:j])
                blocks.append((qualified, block, start + 1))
            i = j
            continue
        i += 1
    return blocks


def _base_public_theorem_names(worktree: Path, base_branch: str, rel_path: str) -> set[str]:
    res = subprocess.run(
        ["git", "show", f"{base_branch}:{rel_path}"],
        cwd=worktree, capture_output=True, text=True, check=False,
    )
    if res.returncode != 0:
        return set()
    return {name for name, _block, _line in _parse_public_theorem_blocks(res.stdout)}


def collect_added_public_theorem_blocks(
    worktree: Path,
    base_branch: str,
) -> list[tuple[str, str, str]]:
    added_lines_by_file = _added_line_numbers_by_file(worktree, base_branch)
    out: list[tuple[str, str, str]] = []
    for rel_path, added_lines in sorted(added_lines_by_file.items()):
        if not rel_path.startswith("lean4/BEDC/") or not rel_path.endswith(".lean"):
            continue
        path = worktree / rel_path
        try:
            text = path.read_text(encoding="utf-8")
        except OSError:
            continue
        base_names = _base_public_theorem_names(worktree, base_branch, rel_path)
        for qualified, block, start_line in _parse_public_theorem_blocks(text):
            if start_line not in added_lines:
                continue
            if qualified in base_names:
                continue
            out.append((qualified, rel_path, block))
    return out


def _probe_payload(stdout: str) -> dict | None:
    try:
        payload = json.loads(stdout)
    except json.JSONDecodeError:
        start = stdout.find("{")
        if start < 0:
            return None
        try:
            decoder = json.JSONDecoder()
            payload, _end = decoder.raw_decode(stdout[start:])
        except json.JSONDecodeError:
            return None
    return payload if isinstance(payload, dict) else None


def detect_one_step_wrapper_probe_hits(worktree: Path, base_branch: str) -> list[str]:
    added_blocks = collect_added_public_theorem_blocks(worktree, base_branch)
    thin_blocks = [
        (qualified, rel_path)
        for qualified, rel_path, block in added_blocks
        if _is_public_thin_wrapper_source(block)
    ]
    if not thin_blocks:
        return []

    rel_by_name = {qualified: rel_path for qualified, rel_path in thin_blocks}
    targets = ",".join(
        f"{_lean_module_from_rel_path(rel_path)}:{qualified}"
        for qualified, rel_path in thin_blocks
    )
    try:
        res = subprocess.run(
            [
                "python3", "lean4/scripts/theorem_wrapper_probe.py",
                "--targets", targets,
            ],
            cwd=worktree,
            capture_output=True,
            text=True,
            check=False,
            timeout=PROBE_TIMEOUT_SECONDS,
        )
    except (subprocess.TimeoutExpired, OSError):
        return []
    if res.returncode != 0:
        return []

    payload = _probe_payload(res.stdout or "")
    if payload is None:
        return []

    hits: list[str] = []
    seen: set[str] = set()
    results = payload.get("results", [])
    if not isinstance(results, list):
        return []
    for row in results:
        if not isinstance(row, dict):
            continue
        if row.get("candidate") is not True or row.get("confidence") != "high":
            continue
        requested = str(row.get("requested_name") or "")
        actual = str(row.get("name") or requested)
        qualified = requested if requested in rel_by_name else actual
        rel_path = rel_by_name.get(qualified)
        if rel_path is None:
            continue
        head = str(row.get("head_constant") or "")
        key = f"{actual}:{head}:{rel_path}"
        if key in seen:
            continue
        seen.add(key)
        hits.append(
            "ONE-STEP THEOREM WRAPPER (proof-term confirmed): "
            f"{actual} forwards to {head} @ {rel_path}"
        )
    return hits


def diff_added_decls(worktree: Path, base_branch: str) -> list[tuple[str, str]]:
    """Return [(name, signature_block)] for theorem/lemma/def added in
    this worktree relative to base_branch, scoped to lean4/BEDC/."""
    res = subprocess.run(
        [
            "git", "log", "-p", "--no-color", "--reverse",
            f"{base_branch}..HEAD", "--", "lean4/BEDC/",
        ],
        cwd=worktree, capture_output=True, text=True, check=False,
    )
    text = res.stdout or ""
    out: list[tuple[str, str]] = []
    pending: list[str] = []
    pending_name: str | None = None
    for raw in text.splitlines():
        if not raw.startswith("+") or raw.startswith("+++"):
            if pending_name is not None and pending:
                out.append((pending_name, "\n".join(pending)))
                pending_name = None
                pending = []
            continue
        line = raw[1:]
        m = DECL_RE.match(line)
        if m:
            if pending_name is not None and pending:
                out.append((pending_name, "\n".join(pending)))
            pending_name = m.group(2)
            pending = [line]
        elif pending_name is not None:
            pending.append(line)
            if len(pending) > SIGNATURE_BLOCK_LIMIT:
                out.append((pending_name, "\n".join(pending)))
                pending_name = None
                pending = []
    if pending_name is not None and pending:
        out.append((pending_name, "\n".join(pending)))
    return out


def declaration_in_derived(worktree: Path, name: str) -> bool:
    res = subprocess.run(
        ["git", "grep", "-l", "-F", f"theorem {name}", "--", DERIVED_PATH_PREFIX],
        cwd=worktree, capture_output=True, text=True, check=False,
    )
    return bool(res.stdout.strip())


# Same regex as codex_formalize.py's _BEDC_TOUCHPOINT_RE — used for the
# SHALLOW GROWTH dup-conclusion preview so codex's self-check sees the
# exact same set as Phase D's reject.
_BEDC_TOUCHPOINT_RE = re.compile(
    r"\b(BHist|BMark|hsame|msame|ProbeBundle|SigRel|InGap|NameCert|"
    r"SemanticNameCert|Cont|Ext|InBundle|UnaryHistory|Pkg|sameSig|"
    r"DescentCertificate|StableTransformation|ThreadFamily|"
    r"AskEvent|AskPolicy|BundleAskPolicy|SealEvent|SealInterface|"
    r"StageInterface|bundleAppend|bundleLength|bwordLength)\b"
)


def _diff_added_blocks_per_file(worktree: Path, base_branch: str) -> dict[str, list[tuple[str, str]]]:
    """Group `diff_added_decls` results by source file (rel path), so the
    SHALLOW GROWTH check can compare conclusions WITHIN one file (matching
    codex_formalize.py's `detect_shallow_growth_patterns` semantics)."""
    # Re-parse the same git log, but track which file each + line lives in.
    res = subprocess.run(
        [
            "git", "log", "-p", "--no-color", "--reverse",
            f"{base_branch}..HEAD", "--", "lean4/BEDC/",
        ],
        cwd=worktree, capture_output=True, text=True, check=False,
    )
    text = res.stdout or ""
    grouped: dict[str, list[tuple[str, str]]] = {}
    current_file: str | None = None
    pending: list[str] = []
    pending_name: str | None = None

    def flush(rel: str | None) -> None:
        nonlocal pending, pending_name
        if rel and pending_name is not None and pending:
            grouped.setdefault(rel, []).append((pending_name, "\n".join(pending)))
        pending_name = None
        pending = []

    for raw in text.splitlines():
        if raw.startswith("+++ b/"):
            flush(current_file)
            current_file = raw[len("+++ b/"):]
            continue
        if not raw.startswith("+") or raw.startswith("+++"):
            flush(current_file)
            continue
        line = raw[1:]
        m = DECL_RE.match(line)
        if m:
            flush(current_file)
            pending_name = m.group(2)
            pending = [line]
        elif pending_name is not None:
            pending.append(line)
            if len(pending) > SIGNATURE_BLOCK_LIMIT:
                flush(current_file)
    flush(current_file)
    return grouped


def _decl_conclusion(block: str) -> str:
    """Extract the conclusion (after the final `:` before `:=`) from a
    declaration's signature block. Same heuristic as codex_formalize.py."""
    header = block.split(":=", 1)[0]
    idx = header.rfind(":")
    if idx == -1:
        return ""
    return " ".join(header[idx + 1:].split())


def detect_shallow_growth_dups(worktree: Path, base_branch: str) -> list[str]:
    """Detect duplicate-conclusion theorems among the round's added decls
    (same algorithm as `codex_formalize.py::detect_shallow_growth_patterns`,
    abbreviated to dup-conclusion only — anchor-missing / parameter-echo
    are already caught by main()). Designed for Phase C self-check use.
    """
    violations: list[str] = []
    grouped = _diff_added_blocks_per_file(worktree, base_branch)
    for rel, blocks in grouped.items():
        conclusion_owner: dict[str, str] = {}
        for name, block in blocks:
            kind_match = re.match(r"\s*(?:protected\s+)?(theorem|lemma)\b", block)
            if not kind_match:
                continue
            conclusion = _decl_conclusion(block)
            if not conclusion:
                continue
            if not _BEDC_TOUCHPOINT_RE.search(conclusion):
                continue
            if conclusion in conclusion_owner:
                violations.append(
                    f"{rel}: duplicate theorem conclusion in "
                    f"{conclusion_owner[conclusion]} and {name}"
                )
            else:
                conclusion_owner[conclusion] = name
    return violations


def added_lean_files(worktree: Path, base_branch: str) -> list[str]:
    res = subprocess.run(
        [
            "git", "diff", "--name-only", "--diff-filter=A",
            f"{base_branch}...HEAD", "--", "lean4/BEDC/",
        ],
        cwd=worktree, capture_output=True, text=True, check=False,
    )
    if res.returncode != 0:
        return []
    return sorted(
        line.strip()
        for line in res.stdout.splitlines()
        if line.strip().startswith("lean4/BEDC/") and line.strip().endswith(".lean")
    )


def detect_large_decide_enumerations(worktree: Path, base_branch: str) -> list[str]:
    violations: list[str] = []
    for rel in added_lean_files(worktree, base_branch):
        path = worktree / rel
        try:
            text = path.read_text(encoding="utf-8")
        except OSError:
            continue
        if not BY_DECIDE_RE.search(text):
            continue
        range_numbers = [int(raw) for raw in LIST_RANGE_NUM_RE.findall(text)]
        nested_ranges = sum(1 for n in range_numbers if n >= 10) >= 3
        foldl_acc_append = "List.range" in text and bool(FOLDL_ACC_APPEND_RE.search(text))
        if nested_ranges or foldl_acc_append:
            violations.append(
                f"{rel}: `by decide` appears with a large List.range enumeration; "
                "use explicit witnesses or a lemma chain"
            )
    return violations


def _has_companion_general_theorem(worktree: Path, rel_path: str, head: str) -> bool:
    """True if the file already carries a parameterised public theorem about the
    same conclusion head — then the value instances are sanity checks, not the
    deliverable, and the cluster is exempt from the value-saturation gate."""
    if not head:
        return False
    try:
        text = (worktree / rel_path).read_text(encoding="utf-8")
    except OSError:
        return False
    for qualified, block, _start in _parse_public_theorem_blocks(text):
        name = qualified.rsplit(".", 1)[-1]
        if VALUE_SUFFIX_RE.search(name):
            continue
        sig = block.split(":=", 1)[0]
        if head in sig and VALUE_BOUND_VAR_RE.search(sig):
            return True
    return False


def _value_instance_key(name: str, namespace: str, block: str) -> tuple[str, str] | None:
    """Return (name_schema, conclusion_head) if `block` is a trivially-closed
    value instance, else None. A candidate is a public theorem whose name or
    conclusion embeds a numeric value, closed by decide/native_decide/rfl, and
    NOT a base/step recursion, a parameterised statement, or a ZMod carrier fact."""
    sig = block.split(":=", 1)[0]
    conclusion = _extract_conclusion(sig)
    if not (VALUE_SUFFIX_RE.search(name) or VALUE_NAT_LITERAL_RE.search(conclusion)):
        return None
    if VALUE_BASE_STEP_RE.search(name):
        return None
    if VALUE_BOUND_VAR_RE.search(sig):
        return None
    if VALUE_ZMOD_EXEMPT_RE.search(sig):
        return None
    if not VALUE_TRIVIAL_PROOF_RE.search(block):
        return None
    name_schema = VALUE_SUFFIX_RE.sub("_{V}", name)
    concl_schema = VALUE_NAT_LITERAL_RE.sub("{N}", " ".join(conclusion.split()))
    head_m = VALUE_HEAD_RE.search(concl_schema)
    return (name_schema, head_m.group(0) if head_m else "")


def detect_value_instance_saturation(worktree: Path, base_branch: str) -> list[str]:
    """Anti-unification family gate. A round MUST NOT satisfy a classical theorem
    target with >=THRESHOLD sibling public theorems that are identical after
    erasing an embedded numeric value, each closed by decide/native_decide/rfl,
    with no companion parameterised theorem.

    Detection is *post-state, introduced-or-worsened* (per the gpt-pro
    adversarial pass), not round-diff-only: a model could otherwise add 2
    instances per round across several rounds and never trip a round-local
    >=THRESHOLD check. We scan each touched file's full current set of public
    theorems, but only FAIL a family that this round pushed to/over the
    threshold (>=1 family member is a round-added decl) — historical debt that
    the round did not worsen is left alone. The beautiful form is one
    forall-theorem binding the mathematical parameter."""
    added = collect_added_public_theorem_blocks(worktree, base_branch)
    # Files this round touched with at least one added value-instance candidate.
    added_names_by_file: dict[str, set[str]] = {}
    for qualified, rel_path, block in added:
        name = qualified.rsplit(".", 1)[-1]
        namespace = qualified.rsplit(".", 1)[0] if "." in qualified else ""
        if _value_instance_key(name, namespace, block) is not None:
            added_names_by_file.setdefault(rel_path, set()).add(name)

    hits: list[str] = []
    for rel_path, added_value_names in sorted(added_names_by_file.items()):
        try:
            text = (worktree / rel_path).read_text(encoding="utf-8")
        except OSError:
            continue
        # Group ALL current public theorems in the file (post-state) by family.
        groups: dict[tuple[str, str], list[str]] = {}
        for qualified, block, _start in _parse_public_theorem_blocks(text):
            name = qualified.rsplit(".", 1)[-1]
            namespace = qualified.rsplit(".", 1)[0] if "." in qualified else ""
            key = _value_instance_key(name, namespace, block)
            if key is None:
                continue
            groups.setdefault(key, []).append(name)
        for (name_schema, head), names in sorted(groups.items()):
            distinct = sorted(set(names))
            if len(distinct) < VALUE_INSTANCE_THRESHOLD:
                continue
            # introduced-or-worsened: this round contributed >=1 family member.
            if not (added_value_names & set(distinct)):
                continue
            if _has_companion_general_theorem(worktree, rel_path, head):
                continue
            hits.append(
                f"{rel_path}: VALUE-INSTANCE SATURATION — {len(distinct)} sibling "
                f"closed computations for `{head}` (schema {name_schema}): "
                + ", ".join(distinct[:8])
                + ". Prove ONE parameterised forall-theorem binding the parameter; "
                "finite checks only as <=2 private examples."
            )

    hits.extend(_detect_pseudo_generalization(added))
    return hits


def _detect_pseudo_generalization(
    added_blocks: list[tuple[str, str, str]],
) -> list[str]:
    """Catch the evasion where the instance table is wrapped in a fake forall:
    `theorem foo (p) (hp : p = 5 ∨ p = 7 ∨ p = 11) := by rcases hp ... decide`.
    A bound variable constrained to a disjunction of >=3 closed values, closed
    by case-split + decide/rfl, is not a general theorem — it is the same value
    instances behind a quantifier."""
    hits: list[str] = []
    for qualified, rel_path, block in added_blocks:
        sig = block.split(":=", 1)[0]
        body = block.split(":=", 1)[1] if ":=" in block else ""
        # Count `_ = <closed value>` disjuncts (∨-separated) in the signature.
        eq_values = re.findall(
            r"=\s*(?:[0-9]+|(?:" + VALUE_WORDS + r")\b)", sig
        )
        n_disjuncts = sig.count("∨") + sig.count(r"\/")
        case_split = bool(re.search(r"\brcases\b|\bmatch\b|\b\|\s*rfl\b", body))
        trivial = bool(re.search(r"\bdecide\b|\bnative_decide\b|\brfl\b", body))
        if len(eq_values) >= 3 and n_disjuncts >= 2 and case_split and trivial:
            name = qualified.rsplit(".", 1)[-1]
            hits.append(
                f"{rel_path}: PSEUDO-GENERALIZATION — `{name}` binds a parameter "
                f"to a disjunction of {len(eq_values)} closed values and discharges "
                "by case-split + decide. This is a value-instance table behind a "
                "quantifier, not a theorem. Prove the unconstrained parameter case."
            )
    return hits


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--worktree", type=Path, required=True)
    p.add_argument("--base-branch", type=str, required=True)
    p.add_argument("--include-shallow", action="store_true",
                    help="Also detect duplicate-conclusion theorems "
                          "(matches codex_formalize.detect_shallow_growth_patterns).")
    args = p.parse_args()

    decls = diff_added_decls(args.worktree, args.base_branch)
    large_decide_hits = detect_large_decide_enumerations(args.worktree, args.base_branch)
    wrapper_hits: list[str] = []
    wrapper_gate_enabled = os.environ.get("BEDC_ENABLE_WRAPPER_GATE", "1") != "0"
    wrapper_gate_shadow = os.environ.get("BEDC_WRAPPER_GATE_SHADOW", "0") == "1"
    if wrapper_gate_enabled:
        wrapper_hits = detect_one_step_wrapper_probe_hits(args.worktree, args.base_branch)
        if wrapper_gate_shadow:
            for hit in wrapper_hits:
                print(f"[shadow] would-reject: {hit}")
            wrapper_hits = []
    # Value-instance saturation gate. Ships SHADOW-first (log would-reject,
    # do not fail) — flip BEDC_VALUE_INSTANCE_GATE_SHADOW=0 to make it a hard
    # gate once production confirms no false positives, mirroring the wrapper
    # gate rollout.
    value_hits: list[str] = []
    value_gate_enabled = os.environ.get("BEDC_ENABLE_VALUE_INSTANCE_GATE", "1") != "0"
    value_gate_shadow = os.environ.get("BEDC_VALUE_INSTANCE_GATE_SHADOW", "1") == "1"
    if value_gate_enabled:
        value_hits = detect_value_instance_saturation(args.worktree, args.base_branch)
        if value_gate_shadow:
            for hit in value_hits:
                print(f"[shadow] would-reject (value-instance): {hit}")
            value_hits = []
    if (
        not decls
        and not args.include_shallow
        and not large_decide_hits
        and not wrapper_hits
        and not value_hits
    ):
        return 0

    arity_hits: list[str] = []
    echo_hits: list[str] = []
    anchor_hits: list[str] = []
    for name, body in decls:
        if MECHANICAL_ARITY_RE.search(name):
            arity_hits.append(name)
            continue
        sig = body.split(":=")[0]
        is_derived = declaration_in_derived(args.worktree, name)
        if PARAMETER_ECHO_BIND_RE.search(sig):
            conclusion = _extract_conclusion(sig)
            if PARAMETER_ECHO_CONCL_RE.search(conclusion):
                concl_no_hsame = _strip_hsame_tokens(conclusion)
                if not BHIST_CONSTRUCTOR_RE.search(concl_no_hsame):
                    echo_hits.append(name)
        # Anchor check matches the orchestrator's
        # detect_decls_without_kernel_touchpoint (codex_formalize.py:2138):
        # scan the full block including body comments, not just the
        # signature. The two gates were previously inconsistent — adding
        # a `-- BEDC touchpoint anchor: BHist BMark` comment satisfied
        # the orchestrator gate but not phase_d_lint, so typeclass
        # instances like `instance fooChapterTasteGate : ChapterTasteGate
        # FooUp` whose signature has no bare `BHist` token would pass
        # orchestrator and fail Phase D. Use the full block here too.
        if is_derived and not BHIST_CONSTRUCTOR_RE.search(body):
            anchor_hits.append(name)

    shallow_hits: list[str] = []
    if args.include_shallow:
        shallow_hits = detect_shallow_growth_dups(args.worktree, args.base_branch)

    if not (
        arity_hits
        or echo_hits
        or anchor_hits
        or shallow_hits
        or large_decide_hits
        or wrapper_hits
        or value_hits
    ):
        return 0

    msgs: list[str] = []
    if arity_hits:
        msgs.append(
            "Mechanical arity suffix on new declaration(s) (NAMING.md §3 forbids"
            " _two/_three/_four/_five/_six/_*_step/_*_witness_chain): "
            + ", ".join(arity_hits[:5])
        )
    if echo_hits:
        msgs.append(
            "Parameter-echo schema: signature binds (name : forall … hsame …) "
            "without anchoring on a concrete BEDC kernel object: "
            + ", ".join(echo_hits[:5])
        )
    if anchor_hits:
        msgs.append(
            "Derived theorem missing a BHist / BMark / hsame / ProbeBundle / "
            "SigRel / NameCert anchor in its signature: "
            + ", ".join(anchor_hits[:5])
        )
    if shallow_hits:
        msgs.append(
            "SHALLOW GROWTH PATTERN — duplicate theorem conclusion(s) "
            "(Phase D will reject):\n  " + "\n  ".join(shallow_hits[:8])
        )
    if large_decide_hits:
        msgs.append(
            "Large enumeration behind `by decide` in added Lean file(s):\n  "
            + "\n  ".join(large_decide_hits[:8])
        )
    if wrapper_hits:
        msgs.append("\n".join(wrapper_hits[:8]))
    if value_hits:
        msgs.append("\n".join(value_hits[:8]))
    print("\n".join(msgs))
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
