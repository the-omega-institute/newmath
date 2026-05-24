#!/usr/bin/env python3
"""Stage 2 writeback: independent Codex reviewer + paper appender.

Runs the killo-golden hygiene prompt through Codex. Codex reads the oracle
transcript and the raw LaTeX block, applies the hygiene checklist, and emits
accept|reject JSON. On accept, this module appends the cleaned LaTeX to the chosen target file
inside `papers/bedc/parts/` (before `\\endinput` if present, else at file end),
then runs `cd papers/bedc && make` once to verify the paper still compiles.

If compile fails, the append is rolled back and Codex is invoked once more
with the pdflatex stderr fed in for retry. After two compile failures the
target is marked stage2_blocked and skipped.
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
import time
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Optional

import verification_axis


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
PROMPTS_DIR = SCRIPT_DIR / "prompts"
LOG_DIR = SCRIPT_DIR / "state" / "stage2_logs"
PAPER_DIR = REPO_ROOT / "papers" / "bedc"

DEFAULT_TIMEOUT = 1800
COMPILE_TIMEOUT = 600
MAX_FILE_LINES = 800
LOGIC_AUDIT_VERSION = "stage2-logic-audit-v1"
INSPIRATION_ONLY_TARGET_RE = re.compile(
    r"^papers/bedc/parts/(?:visions|conjectures)/",
    re.IGNORECASE,
)
BODY_ENV_RE = re.compile(
    r"\\begin\{(theorem|lemma|proposition|corollary|definition)\}"
)
PROOF_ENV_RE = re.compile(r"\\begin\{proof\}")
EXTERNAL_PROVENANCE_PATTERNS = [
    re.compile(r"Inspired by Omega Project"),
    re.compile(r"\b[Aa]utomath\b"),
    re.compile(r"automath/"),
    re.compile(r"discovery(?:\\_|\s*_)report\.json"),
    re.compile(r"tools[\\/]+automath_newmath_bridge[\\/]+review_packets[\\/]+[^}\s]+\.json"),
    re.compile(r"review_packets[\\/]+[^}\s]+\.json"),
    re.compile(r"https?://"),
    re.compile(r"github\.com", re.IGNORECASE),
    re.compile(r"\barxiv\b", re.IGNORECASE),
    re.compile(r"\bWikipedia\b", re.IGNORECASE),
    re.compile(r"\b(ChatGPT|Claude|OpenAI|Anthropic)\b"),
    re.compile(r"(?:^|[\s{(])/(?:Users|private|tmp|var|opt|home)/"),
    re.compile(r"\b(?:Generated|Produced)\s+by\s+(?:ChatGPT|Claude|OpenAI|Anthropic)\b", re.IGNORECASE),
    re.compile(r"\b(?:repository|repo)\s+coordinates\b", re.IGNORECASE),
    re.compile(r"\b(?:source|repository|repo)[_-](?:path|repo|commit|ref)\b", re.IGNORECASE),
    re.compile(r"\b(?:review|bridge)\s+packet\s+(?:path|json)\b", re.IGNORECASE),
]


@dataclass
class WritebackResult:
    ok: bool
    verdict: str
    tex_file: str
    appended: bool
    compile_ok: bool
    rejection_reasons: list
    rejection_codes: list = None  # type: ignore
    error: str = ""
    # On verdict=="compile_failed", carries a compact extract of pdflatex's
    # real error lines (Undefined control seq / Missing / Extra etc.) so
    # the runtime can feed them as rejection_reasons to codex corrective.
    compile_errors: list = None  # type: ignore
    closure_candidate: dict = None  # type: ignore
    logic_audit: dict = None  # type: ignore


def _now_tag() -> str:
    return datetime.now().strftime("%Y%m%d_%H%M%S")


def _extract_json_object(text: str) -> Optional[dict]:
    text = (text or "").strip()
    if not text:
        return None
    fence = re.search(r"```(?:json)?\s*(\{.*?\})\s*```", text, flags=re.DOTALL)
    if fence:
        try:
            return json.loads(fence.group(1))
        except json.JSONDecodeError:
            pass
    # Fallback: scan forward from each '{' looking for a balanced JSON object
    # that parses. Robust against prose-embedded braces (e.g. math subscripts
    # like _{l,u}) that would defeat a naive first-{-to-last-} substring.
    for start in range(len(text)):
        if text[start] != "{":
            continue
        depth = 0
        in_str = False
        esc = False
        for i in range(start, len(text)):
            ch = text[i]
            if in_str:
                if esc:
                    esc = False
                elif ch == "\\":
                    esc = True
                elif ch == '"':
                    in_str = False
                continue
            if ch == '"':
                in_str = True
            elif ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
                if depth == 0:
                    candidate = text[start : i + 1]
                    try:
                        return json.loads(candidate)
                    except json.JSONDecodeError:
                        break
    return None


def codex_json_fallback(
    prompt: str,
    *,
    timeout: int = DEFAULT_TIMEOUT,
    log_tag: str = "",
    role_note: str = "Run this BEDC gate through Codex.",
) -> tuple[bool, dict, str, str]:
    """Run an independent read-only Codex JSON gate."""
    import codex_orchestrator

    fallback_prompt = (
        f"{role_note}\n"
        "Act as the independent checker for this gate. Preserve the "
        "same acceptance standard and return only the JSON object required by "
        "the original prompt. Do not edit files.\n\n"
        f"{prompt}"
    )
    tag = (log_tag or "stage2") + "_codex_gate"
    result = codex_orchestrator.codex_exec(
        fallback_prompt,
        timeout=timeout,
        log_tag=tag,
    )
    if not result.ok:
        return (False, {}, result.raw_output, result.error or f"codex rc={result.rc}")
    parsed = result.parsed or _extract_json_object(result.raw_output) or {}
    if not parsed:
        return (False, {}, result.raw_output, "codex gate output was not JSON")
    return (True, parsed, result.raw_output, "")


def _all_paper_labels() -> set[str]:
    """Return all \\label{X} values from papers/bedc/parts/**/*.tex.

    Recomputed each call (~500ms). We do not cache because pipeline
    writebacks append content to existing .tex files without updating
    parent-dir mtime, so cache invalidation is unreliable. Per-call
    cost is acceptable: writebacks happen every 5-10 min.
    """
    parts = REPO_ROOT / "papers" / "bedc" / "parts"
    if not parts.exists():
        return set()
    labels: set[str] = set()
    for path in parts.rglob("*.tex"):
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        labels.update(re.findall(r"\\label\{([^}]+)\}", text))
    return labels


def _detect_dangling_autorefs(content: str) -> list[str]:
    """Return list of \\autoref{X} / \\ref{X} citations whose label is
    not present anywhere in papers/bedc/parts/. Excludes refs to labels
    defined IN the candidate content itself (forward refs within the
    new block are valid)."""
    cited = set(re.findall(r"\\autoref\{([^}]+)\}", content))
    cited.update(re.findall(r"(?<!\\auto)\\ref\{([^}]+)\}", content))
    if not cited:
        return []
    own_labels = set(re.findall(r"\\label\{([^}]+)\}", content))
    cited -= own_labels
    paper_labels = _all_paper_labels()
    missing = sorted(cited - paper_labels)
    return missing


def _detect_external_provenance(content: str) -> list[str]:
    """Return paper-body lines that leak bridge/source metadata."""
    violations: list[str] = []
    for line_no, line in enumerate((content or "").splitlines(), start=1):
        for pattern in EXTERNAL_PROVENANCE_PATTERNS:
            if pattern.search(line):
                violations.append(f"line {line_no}: {line.strip()[:220]}")
                break
    return violations


def _logic_surface_audit(content: str) -> dict:
    """Return warnings-only post-write logic-discipline surface signals.

    This is deliberately not an accept/reject gate.  Stage 2 already has
    hygiene, provenance, and compile gates; this audit only records likely
    surfaces where the 12 BEDC/NewMath discipline rules deserve later review.
    """
    text = content or ""
    low = text.lower()
    warnings: list[dict[str, str]] = []

    def add(code: str, detail: str) -> None:
        warnings.append({"code": code, "detail": detail})

    theorem_envs = re.findall(
        r"\\begin\{(theorem|lemma|proposition|corollary)\}",
        text,
    )
    proof_count = len(PROOF_ENV_RE.findall(text))
    label_count = len(re.findall(r"\\label\{[^}]+\}", text))

    if theorem_envs and proof_count == 0:
        add(
            "theorem_surface_without_proof_env",
            "theorem-shaped content has no proof environment; confirm it is an intentional statement-only landing",
        )

    if re.search(r"\\exists\b|\bthere exists\b|\bexistence\b", low):
        if not re.search(r"\b(witness|take|choose|chosen|let|given by|defined by|construct|constructed|set)\b", low):
            add(
                "existence_surface_without_witness_cue",
                "existence language appears without an obvious witness/extractor cue",
            )

    if re.search(r"\b(bridge|transport|continuation|embedding|projection|interpretation|mirror)\b|\\[hmp]same\b", low):
        if not re.search(
            r"\b(eliminat|cut|factor|intermediate|compose|composition|reduce|through)\b"
            r"|\b(project|projection|projecting|unfold|unfolding|unfolded|repack|repacking)\b"
            r"|\\autoref\{[^}]*transport[^}]*\}"
            r"|finite observation|common observation|consumer-facing|displayed coordinates|displayed classifier",
            low,
        ):
            add(
                "bridge_surface_without_elimination_cue",
                "bridge/transport surface appears without an obvious elimination, cut, or factorization cue",
            )

    if re.search(r"\b(limit|completion|compactness|continuity|cauchy|convergen)\b", low):
        if not re.search(
            r"\b(rate|modulus|bound|bounded|tail|finite cover|finite subcover|covering|cofinal)\b"
            r"|finite[- ]window|finite observation|finite submesh|finite mesh|finite request|displayed finite"
            r"|non[- ]escape|cannot recover|without adding any analytic object|excluded (?:limit|completion)"
            r"|outside (?:the )?(?:meet )?packet|no ambient completeness|ambient .*completeness theorem",
            low,
        ):
            add(
                "completion_surface_without_rate_modulus_cue",
                "limit/completion/compactness surface appears without an obvious rate, modulus, bound, or finite-cover cue",
            )

    if re.search(r"\b(previous|earlier|above|ambient|context)\b", low) and "\\autoref{" not in text:
        add(
            "dependency_surface_without_reference_cue",
            "dependency prose appears without an explicit local autoref cue",
        )

    return {
        "version": LOGIC_AUDIT_VERSION,
        "warning_count": len(warnings),
        "warnings": warnings[:12],
        "surface": {
            "theorem_env_count": len(theorem_envs),
            "proof_env_count": proof_count,
            "label_count": label_count,
            "line_count": len(text.splitlines()),
        },
    }


def _body_env_names(content: str) -> list[str]:
    return BODY_ENV_RE.findall(content or "")


def _has_body_env(content: str) -> bool:
    return bool(_body_env_names(content))


def _deterministic_theory_rejections(
    content: str,
    *,
    target_title: str,
    target_tex_file: str,
) -> tuple[list[str], list[str]]:
    """Return local Stage 2 theory-shape rejections before any LLM gate.

    These checks are intentionally narrow: they catch cases the current
    append-only writeback cannot repair and cases that are almost always
    template surface generation rather than one minimal BOARD target.
    """
    text = content or ""
    reasons: list[str] = []
    codes: list[str] = []

    def reject(code: str, reason: str) -> None:
        codes.append(code)
        reasons.append(reason)

    envs = _body_env_names(text)
    axis_hits = verification_axis.verification_axis_hits(
        " ".join([target_title or "", text]),
        allow_negated_sentences=True,
    )
    if axis_hits:
        reject(
            "verification_axis_surface",
            "Stage 2 paper-content writeback rejects Lean / verification-axis "
            "surface text; this lane must deepen BEDC-native content only "
            f"({', '.join(axis_hits[:6])}).",
        )

    if len(envs) > 1:
        reject(
            "not_minimal_multiple_surfaces",
            "Stage 2 accepts one minimal theorem-like or definition-like "
            f"surface per BOARD target; candidate has {len(envs)} body "
            f"environments: {', '.join(envs[:8])}.",
        )

    target = _resolve_target_tex(target_tex_file)
    if target is not None and _has_body_env(text):
        try:
            target_text = target.read_text(encoding="utf-8", errors="replace")
        except OSError:
            target_text = ""
        closure_start = target_text.find("\\begin{closurestatus}")
        endinput_start = target_text.find("\\endinput")
        closure_is_before_append_point = (
            closure_start >= 0
            and (endinput_start < 0 or closure_start < endinput_start)
        )
        if closure_is_before_append_point:
            reject(
                "append_after_closurestatus",
                "The selected target file already has a closurestatus block "
                "before the append point, so append-only Stage 2 would place "
                "new body content after the chapter status.",
            )

    title_low = (target_title or "").lower()
    text_low = text.lower()
    relation_vocab = (
        "substrate",
        "bisimulation",
        "mirror",
        "classifier alignment",
        "forgetful",
        "source-equivalence",
    )
    if any(term in text_low or term in title_low for term in relation_vocab):
        concrete_cues = (
            "row map",
            "displayed row",
            "displayed coordinate",
            "carrier row",
            "receiver",
            "receiving",
            "consumer-facing",
            "\\autoref{",
        )
        if not any(cue in text_low for cue in concrete_cues):
            reject(
                "template_relation_surface",
                "Relation vocabulary appears without a concrete receiving "
                "carrier row map, displayed row, or local reference tying the "
                "surface to the target object.",
            )

    return reasons, codes


def _resolve_target_tex(suggested: str) -> Optional[Path]:
    if not suggested:
        return None
    rel = suggested.strip().replace("\\", "/")
    if INSPIRATION_ONLY_TARGET_RE.search(rel):
        return None
    candidate = (REPO_ROOT / suggested).resolve()
    try:
        candidate.relative_to(REPO_ROOT / "papers" / "bedc" / "parts")
    except ValueError:
        return None
    if not candidate.exists() or not candidate.is_file():
        return None
    text = candidate.read_text(encoding="utf-8", errors="replace")
    if "\\input" in text and "\\begin{theorem}" not in text and "\\begin{definition}" not in text:
        return None
    return candidate


def _append_to_tex(target: Path, content: str) -> tuple[bool, str]:
    """Append content before \\endinput if present, else at file end. Returns (ok, backup_text).

    Atomic write via temp + replace so a crash mid-write never leaves the
    paper file truncated."""
    original = target.read_text(encoding="utf-8")
    block = "\n\n" + content.rstrip() + "\n"
    if "\\endinput" in original:
        new_text = original.replace("\\endinput", block + "\\endinput", 1)
    else:
        new_text = original.rstrip() + block
    new_lines = new_text.count("\n") + 1
    if new_lines > MAX_FILE_LINES:
        return (False, original)
    tmp = target.with_suffix(target.suffix + ".tmp")
    tmp.write_text(new_text, encoding="utf-8")
    tmp.replace(target)
    return (True, original)


def _make_paper() -> tuple[bool, str]:
    if not (PAPER_DIR / "Makefile").exists():
        return (True, "(no Makefile; skipping compile)")
    from locks import file_lock
    with file_lock("paper_make"):
        proc = subprocess.run(
            ["make"],
            cwd=str(PAPER_DIR),
            capture_output=True,
            text=True,
            timeout=COMPILE_TIMEOUT,
        )
    out = (proc.stdout or "") + "\n" + (proc.stderr or "")
    if proc.returncode != 0:
        out = out.rstrip() + "\n\n" + _paper_compile_log_excerpt()
    return (proc.returncode == 0, out)


def _paper_compile_log_excerpt() -> str:
    """Return a compact diagnostic excerpt from papers/bedc/main.log."""
    log_path = PAPER_DIR / "main.log"
    if not log_path.exists():
        return "## main.log diagnostic excerpt\n(no papers/bedc/main.log found)"
    text = log_path.read_text(encoding="utf-8", errors="replace")
    lines = text.splitlines()
    hits: list[int] = []
    patterns = (
        "Undefined control sequence",
        "LaTeX Error",
        "Emergency stop",
        "Fatal error",
        "Runaway argument",
        "File ended while scanning",
    )
    for i, line in enumerate(lines):
        stripped = line.strip()
        if stripped.startswith("!") or any(p in line for p in patterns):
            if any(font in line for font in ("OML/lmm", "OT1/lmr", "OMS/lmsy", "OMX/lmex")):
                continue
            hits.append(i)
    if not hits:
        tail = lines[-80:]
        return "## main.log diagnostic excerpt\n(no focused TeX error lines found; tail follows)\n" + "\n".join(tail)

    chunks: list[str] = ["## main.log diagnostic excerpt"]
    seen: set[int] = set()
    for hit in hits[:8]:
        start = max(0, hit - 2)
        end = min(len(lines), hit + 6)
        for idx in range(start, end):
            if idx in seen:
                continue
            seen.add(idx)
            chunks.append(lines[idx])
        chunks.append("---")
    return "\n".join(chunks).rstrip("-\n")


def writeback(
    *,
    target_id: str,
    target_title: str,
    transcript_dir: Path,
    raw_latex_path: Path,
    suggested_target_tex: str,
) -> WritebackResult:
    """Stage 2 writeback with mandatory killo-golden review.

    Pipeline order:
      1. Read and extract the candidate LaTeX block.
      2. Run hygiene_normalize.normalize() for mechanical fixes.
      3. Apply narrow deterministic theory-shape rejections that append-only
         Stage 2 cannot repair safely.
      4. Always run the killo-golden reviewer through Codex.
      5. On accept, atomically append and run `make`; compile failure rolls
         the append back.
    """
    import hygiene_normalize

    raw_text = raw_latex_path.read_text(encoding="utf-8") if raw_latex_path.exists() else ""

    # Extract the LaTeX block from raw_text. Oracle output may have
    # surrounding prose / `Insertion target:` line. We split before
    # normalizing.
    fenced = re.search(r"```(?:latex)?\s*(.*?)```", raw_text, re.DOTALL)
    if fenced:
        latex_body = fenced.group(1)
    else:
        # Heuristic: take from first \begin{theorem|lemma|...} to last \end of same.
        first = re.search(r"\\begin\{(?:theorem|lemma|proposition|corollary|definition)\}", raw_text)
        if first:
            latex_body = raw_text[first.start():]
        else:
            latex_body = raw_text

    # ── Step 1-3: auto-normalize ──
    norm = hygiene_normalize.normalize(
        latex_body,
        preamble_path=REPO_ROOT / "papers" / "bedc" / "preamble.tex",
    )

    # Persist normalized content back so corrective retries (or human
    # inspection) see the fixed version.
    if norm.changed:
        # Replace the LaTeX block in raw_text, preserving any surrounding
        # `Insertion target:` line.
        if fenced:
            new_raw = raw_text.replace(fenced.group(0),
                                        f"```latex\n{norm.content}\n```")
        else:
            # If we extracted by env-detect, only persist if difference is meaningful
            new_raw = norm.content if not raw_text.endswith(latex_body) else \
                      raw_text[: -len(latex_body)] + norm.content
        try:
            raw_latex_path.write_text(new_raw, encoding="utf-8")
        except OSError:
            pass

    # ── Step 3.5: scan for dangling \autoref / \ref ──
    # This is repo-aware (needs to grep all paper labels), so it lives
    # here rather than inside hygiene_normalize. Missing refs ALWAYS
    # force the review path so the gate has a chance to either
    # fix typos via Grep or reject with a precise rejection reason.
    dangling_refs = _detect_dangling_autorefs(norm.content)
    extra_blocking_issues: list[str] = []
    if dangling_refs:
        extra_blocking_issues.append(
            "dangling autoref(s): the following \\autoref / \\ref citations "
            "have no \\label{X} anywhere under papers/bedc/parts/: "
            + ", ".join(dangling_refs[:8])
            + (f" (and {len(dangling_refs) - 8} more)" if len(dangling_refs) > 8 else "")
        )
    external_provenance = _detect_external_provenance(norm.content)
    logic_audit = _logic_surface_audit(norm.content)
    if external_provenance:
        return WritebackResult(
            False,
            "reject",
            suggested_target_tex,
            False,
            False,
            [
                "external provenance leaked into paper body: Automath / bridge / "
                "discovery JSON records are candidate metadata only; re-derive as "
                "BEDC-native content. "
                + "; ".join(external_provenance[:5])
            ],
            rejection_codes=["external_provenance_leak"],
            logic_audit=logic_audit,
        )

    local_reasons, local_codes = _deterministic_theory_rejections(
        norm.content,
        target_title=target_title,
        target_tex_file=suggested_target_tex,
    )
    if local_reasons:
        return WritebackResult(
            False,
            "reject",
            suggested_target_tex,
            False,
            False,
            local_reasons,
            rejection_codes=local_codes,
            logic_audit=logic_audit,
        )

    # ── Step 4: mandatory killo-golden review ──
    # Blocking issues are things normalize cannot mechanically fix:
    # missing environment, unbalanced begin/end, Chinese chars, dangling
    # autorefs, BEDC-relation-as-function misuses, transport-without-citation.
    # Even when this list is empty, the independent reviewer still checks
    # minimality, target locality, and theory load before writeback.
    rejection_reasons: list[str] = []
    all_blocking = list(norm.blocking_issues) + extra_blocking_issues
    template = (PROMPTS_DIR / "killo_golden_writeback.txt").read_text(encoding="utf-8")

    def _safe(s: str) -> str:
        return (s or "").replace("{", "{{").replace("}", "}}")

    prompt = template.format(
        target_id=_safe(target_id),
        target_title=_safe(target_title),
        transcript_dir=_safe(str(transcript_dir)),
        raw_latex_path=_safe(str(raw_latex_path)),
        target_tex_file=_safe(suggested_target_tex),
        repo_root=_safe(str(REPO_ROOT)),
    )
    prompt += "\n\n## Auto-normalize report (already applied)\n"
    if norm.transformations:
        for t in norm.transformations:
            prompt += f"- {t}\n"
    else:
        prompt += "- none\n"
    prompt += "\n## Blocking issues (require your judgement)\n"
    if all_blocking:
        for b in all_blocking:
            prompt += f"- {b}\n"
    else:
        prompt += "- none\n"

    log_tag = f"writeback_{target_id}"
    parsed: dict = {}
    fallback_ok, parsed, stdout, fallback_error = codex_json_fallback(
        prompt,
        log_tag=log_tag,
        role_note=(
            "Run the BEDC killo-golden writeback gate as the primary Codex "
            "gate; apply the same hygiene, minimality, and theory-safety "
            "standard, return only JSON, and do not edit files."
        ),
    )
    if not fallback_ok:
        return WritebackResult(False, "error", "", False, False, [],
                                error=f"codex killo-golden failed: {fallback_error[:400]}",
                                logic_audit=logic_audit)
    if not parsed:
        return WritebackResult(False, "error", "", False, False, [],
                                error="codex killo-golden output was not JSON",
                                logic_audit=logic_audit)
    verdict = str(parsed.get("verdict", "")).lower()
    rejection_reasons = parsed.get("rejection_reasons") or []
    if verdict != "accept":
        return WritebackResult(True, "reject", "", False, False, list(rejection_reasons),
                               rejection_codes=["killo_review_reject"],
                               logic_audit=logic_audit)
    content = str(parsed.get("content") or norm.content)
    tex_rel = str(parsed.get("tex_file") or suggested_target_tex)
    logic_audit = _logic_surface_audit(content)
    post_external_provenance = _detect_external_provenance(content)
    if post_external_provenance:
        return WritebackResult(
            False,
            "reject",
            tex_rel,
            False,
            False,
            [
                "external provenance leaked into accepted paper body: "
                + "; ".join(post_external_provenance[:5])
            ],
            rejection_codes=["external_provenance_leak"],
            logic_audit=logic_audit,
        )
    post_local_reasons, post_local_codes = _deterministic_theory_rejections(
        content,
        target_title=target_title,
        target_tex_file=tex_rel,
    )
    if post_local_reasons:
        return WritebackResult(
            False,
            "reject",
            tex_rel,
            False,
            False,
            post_local_reasons,
            rejection_codes=post_local_codes,
            logic_audit=logic_audit,
        )

    # ── Step 5: atomic append + make verify ──

    target = _resolve_target_tex(tex_rel)
    if target is None:
        return WritebackResult(False, "reject", tex_rel, False, False,
                                ["resolved tex_file is not a concrete body file"],
                                rejection_codes=["bad_target_file"],
                                logic_audit=logic_audit)

    if not content.strip():
        return WritebackResult(False, "reject", tex_rel, False, False, ["empty content"],
                                rejection_codes=["empty_content"],
                                logic_audit=logic_audit)

    from locks import file_lock
    with file_lock("paper_writes"):
        appended, original = _append_to_tex(target, content)
        if not appended:
            return WritebackResult(False, "reject", tex_rel, False, False,
                                    [f"append would exceed {MAX_FILE_LINES} lines"],
                                    rejection_codes=["line_cap"],
                                    logic_audit=logic_audit)

        compile_ok, compile_log = _make_paper()
        if not compile_ok:
            tmp = target.with_suffix(target.suffix + ".rollback.tmp")
            tmp.write_text(original, encoding="utf-8")
            tmp.replace(target)
            log_path = LOG_DIR / f"compile_fail_{target_id}_{_now_tag()}.log"
            log_path.parent.mkdir(parents=True, exist_ok=True)
            log_path.write_text(compile_log, encoding="utf-8")
            errors = _extract_compile_errors(compile_log)
            return WritebackResult(
                True, "compile_failed",
                str(target.relative_to(REPO_ROOT)),
                False, False, [],
                rejection_codes=["compile_failed"],
                compile_errors=errors,
                logic_audit=logic_audit,
            )

    tex_result = str(target.relative_to(REPO_ROOT))
    closure_review: dict = {}
    try:
        import closure_candidate

        closure_review = closure_candidate.analyze(
            target_id=target_id,
            target_title=target_title,
            tex_file=tex_result,
            appended_content=content,
        )
    except Exception as exc:
        closure_review = {
            "ok": False,
            "action": "error",
            "error": f"closure_candidate failed: {exc}",
        }

    return WritebackResult(True, "accept", tex_result, True, True, [],
                           rejection_codes=[],
                           closure_candidate=closure_review,
                           logic_audit=logic_audit)


def _extract_compile_errors(compile_log: str) -> list[str]:
    """Pluck real pdflatex/precheck errors out of the noisy compile log.

    Returns a deduplicated list of error lines + their line context (`l.NNN`
    line) suitable to feed back to codex as rejection_reasons. Filters out
    Overfull/Underfull hbox warnings and font diagnostics that aren't real
    errors."""
    if not compile_log:
        return []
    out: list[str] = []
    seen: set[str] = set()
    lines = compile_log.splitlines()

    def add(msg: str) -> None:
        msg = msg.strip()[:400]
        if msg and msg not in seen:
            seen.add(msg)
            out.append(msg)

    for i, line in enumerate(lines):
        stripped = line.strip()
        if stripped.startswith("DUPLICATE \\leanchecked / \\leantarget"):
            ctx = []
            for j in range(i + 1, min(i + 5, len(lines))):
                cl = lines[j].strip()
                if cl:
                    ctx.append(cl)
            add(stripped + (" | " + " ; ".join(ctx) if ctx else ""))
        elif stripped.startswith("Fix: keep one canonical site with \\leanchecked / \\leantarget"):
            add(stripped)
        if len(out) >= 8:
            return out

    skip_prefixes = (
        "Overfull \\hbox", "Underfull \\hbox", "Overfull \\vbox", "Underfull \\vbox",
        "LaTeX Font Warning",
    )
    for i, line in enumerate(lines):
        stripped = line.strip()
        if not stripped.startswith("!"):
            continue
        # Skip font-related ! diagnostics (those long OML/lmm lines)
        if any(s in line for s in ("OML/lmm", "OT1/lmr", "OMS/lmsy", "OMX/lmex")):
            continue
        if any(stripped.startswith(p) for p in skip_prefixes):
            continue
        # Get the next 1-2 lines for context (often `l.NNN ...` location)
        ctx = []
        for j in range(i + 1, min(i + 3, len(lines))):
            cl = lines[j].strip()
            if cl.startswith("l.") or "Undefined" in cl or "Missing" in cl:
                ctx.append(cl[:200])
        add(stripped + " | " + " ; ".join(ctx))
        if len(out) >= 8:  # cap; codex doesn't need 50 errors
            break
    return out


def main() -> int:
    import argparse

    parser = argparse.ArgumentParser(description="Stage 2 killo-golden writeback")
    parser.add_argument("target_id", help="BEDC target id, e.g. B-01")
    parser.add_argument("--title", default="")
    parser.add_argument("--transcript-dir", required=True)
    parser.add_argument("--raw-latex", required=True, help="path to raw LaTeX file from oracle terminal turn")
    parser.add_argument("--suggested-tex", default="", help="codex/oracle-suggested target body file")
    args = parser.parse_args()

    result = writeback(
        target_id=args.target_id,
        target_title=args.title,
        transcript_dir=Path(args.transcript_dir),
        raw_latex_path=Path(args.raw_latex),
        suggested_target_tex=args.suggested_tex,
    )
    print(json.dumps({
        "ok": result.ok,
        "verdict": result.verdict,
        "tex_file": result.tex_file,
        "appended": result.appended,
        "compile_ok": result.compile_ok,
        "rejection_reasons": result.rejection_reasons,
        "rejection_codes": result.rejection_codes or [],
        "error": result.error,
        "compile_errors": result.compile_errors or [],
        "closure_candidate": result.closure_candidate or {},
        "logic_audit": result.logic_audit or {},
    }, indent=2, ensure_ascii=False))
    return 0 if result.ok and result.verdict == "accept" else 1


if __name__ == "__main__":
    raise SystemExit(main())
