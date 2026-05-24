#!/usr/bin/env python3
"""BOARD spawn gate — combine codex + oracle candidates and append accepted ones.

Two upstream sources:
- codex track collects board_candidates throughout its rounds (lemmas /
  corollaries / structural variants noticed while proving).
- oracle track, after self-declaring proved, runs an "adjacent directions"
  prompt that surfaces extension / counterpart / sibling research directions.

This module merges both lists, dedups against existing BOARD and paper
coverage, then runs a Codex maker/checker judge for candidates that cannot
be admitted by deterministic local gates. Candidates that are promising but not yet
executable are held in candidate_inbox for later refinement instead of being
thrown away. Accepted candidates are atomically appended to local BOARD.md;
the supervisor commit path keeps BOARD files local-only.

Replaces the old Stage 1.5 single-source codex.discover_topics flow.
"""

from __future__ import annotations

import json
import re
import time
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Optional

from dispatch_bedc_target import SCRIPT_DIR, REPO_ROOT, BOARD_PATH
from locks import file_lock
import codex_orchestrator
import board_archive
import board_context
import candidate_inbox
import candidate_substance
import paper_index
import logic_packet_gate


PROMPTS_DIR = SCRIPT_DIR / "prompts"
LOG_DIR = SCRIPT_DIR / "state" / "board_spawn_logs"
LATEST_STATUS_PATH = SCRIPT_DIR / "state" / "board_spawn_latest.json"

DEFAULT_JUDGE_TIMEOUT = 600

DEFAULT_FIT_THRESHOLD = 7
DEFAULT_NOVELTY_THRESHOLD = 6
EXTERNAL_SIGNAL_RE = re.compile(
    r"Automath|automath|Bridge continuation target|Automath continuation|"
    r"bridge_consumption_mode|review_packets?|discovery_report|"
    r"external theorem signal|source theorem signal",
    re.IGNORECASE,
)
LANDING_KINDS = {
    "existing_chapter_lemma",
    "existing_chapter_obligation",
    "existing_chapter_ledger_row",
    "new_chapter",
    "reject",
}
PRE_TASTEGATE_REQUIRED_FIELDS = {
    "carrier_surface": ("carrier", 40),
    "classifier_surface": ("classifier", 40),
    "nontrivial_witness_plan": ("nontrivial witness", 40),
    "field_faithful_plan": ("field faithful projection", 40),
    "structural_atomicity": ("structural atomicity", 40),
    "falsifiable_prediction": ("falsifiable prediction", 30),
    "independence_witness": ("independence witness", 30),
    "elimination_plan": ("elimination plan", 30),
}
PRE_TASTEGATE_OPTIONAL_FIELDS = (
    "tastegate_mode",
    "ripeness_risk",
    "conjecture_fallback",
)
LOGIC_PACKET_FIELDS = (
    "axiom_budget",
    "strength_level",
    "budget_reason",
    "witness_extractor",
    "existence_mode",
    "cut_rank",
    "elimination_plan",
    "equality_kind",
    "interpretation_kind",
    "resource_trace",
    "dependency_trace",
    "rate_modulus_surface",
    "oracle_mode",
)
DETERMINISTIC_FALLBACK_SOURCES = {
    "plain_math_review",
    "research_lane:burden_candidate_miner",
    "research_lane:paper_gap_scanner",
    "research_lane:candidate_inbox",
}
ANTI_PARAMETER_ECHO_RE = re.compile(
    r"local obligation row projection|parameter[- ]echo|"
    r"displayed namecert obligation surface.*(?:contains|records).*displayed|"
    r"merely restates|tautological re[- ]projection|"
    r"generic per[- ]seal projection",
    re.IGNORECASE,
)
DETERMINISTIC_ALLOWED_LANDING = {
    "existing_chapter_lemma",
    "existing_chapter_obligation",
    "existing_chapter_ledger_row",
}
DIRECT_CODEX_SOURCES = {
    "automath_newmath_bridge",
    "codex",
    "plain_math_review",
    "paper_review",
    "research_lane:burden_candidate_miner",
    "research_lane:paper_gap_scanner",
    "research_lane:candidate_inbox",
}


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _now_tag() -> str:
    return datetime.now().strftime("%Y%m%d_%H%M%S")


def _safe(text: str) -> str:
    return (text or "").replace("{", "{{").replace("}", "}}")


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


def _codex_json_fallback(
    prompt: str,
    *,
    timeout: int,
    log_tag: str,
    role_note: str,
) -> tuple[bool, dict, str, str]:
    fallback_prompt = (
        f"{role_note}\n"
        "Act as the independent BOARD judge. Preserve the same "
        "fit/novelty thresholds, reject when uncertain, return only the JSON "
        "object requested by the original prompt, and do not edit files.\n\n"
        f"{prompt}"
    )
    result = codex_orchestrator.codex_exec(
        fallback_prompt,
        timeout=timeout,
        log_tag=f"{log_tag}_codex_gate",
    )
    if not result.ok:
        return (False, {}, result.raw_output, result.error or f"codex rc={result.rc}")
    parsed = result.parsed or _extract_json_object(result.raw_output) or {}
    if not parsed:
        return (False, {}, result.raw_output, "codex gate output was not JSON")
    return (True, parsed, result.raw_output, "")


# ---------------------------------------------------------------------------
# Existing BOARD / paper coverage discovery
# ---------------------------------------------------------------------------


def _existing_board_titles() -> set[str]:
    """Lowercased existing target titles for dedup."""
    return board_archive.existing_target_titles(include_archive=True)


def _existing_board_ids() -> list[str]:
    return board_archive.existing_target_ids(include_archive=True)


def _next_target_id(also_accepted: list[str]) -> str:
    ids = _existing_board_ids() + list(also_accepted)
    nums = [int(i.split("-")[1]) for i in ids if i.startswith("B-")]
    next_num = (max(nums) + 1) if nums else 1
    return f"B-{next_num:02d}"


# ---------------------------------------------------------------------------
# Judge: Codex maker/checker on combined candidate list
# ---------------------------------------------------------------------------


@dataclass
class BoardSpawnResult:
    ok: bool
    accepted: list[dict] = field(default_factory=list)
    held: list[dict] = field(default_factory=list)
    rejected: list[dict] = field(default_factory=list)
    appended_ids: list[str] = field(default_factory=list)
    error: str = ""
    error_kind: str = ""


def classify_judge_error(error: str) -> str:
    """Return a stable outage kind for BOARD judge failures."""
    low = (error or "").lower()
    if not low:
        return ""

    codex_kind = ""
    if "codex" in low:
        codex_kind = "codex_failed"
        if "failed to initialize in-process app-server client" in low:
            codex_kind = "codex_sandbox_init_failed"
        elif "operation not permitted" in low:
            codex_kind = "codex_operation_not_permitted"
        elif "output was not json" in low:
            codex_kind = "codex_non_json"
        elif "codex exec rc=-9" in low or "timed out" in low:
            codex_kind = "codex_timeout"

    if codex_kind:
        return f"board_judge_unavailable:{codex_kind}"
    return "board_judge_failed"


def _now_iso() -> str:
    return datetime.now().astimezone().isoformat(timespec="seconds")


def _write_latest_status(
    *,
    result: BoardSpawnResult,
    codex_input: int,
    oracle_input: int,
    codex_alive: int,
    oracle_alive: int,
    cheap_drop_count: int,
) -> None:
    LATEST_STATUS_PATH.parent.mkdir(parents=True, exist_ok=True)
    error = " ".join(str(result.error or "").split())[:500]
    record = {
        "ts": _now_iso(),
        "ok": result.ok,
        "codex_input": codex_input,
        "oracle_input": oracle_input,
        "codex_alive": codex_alive,
        "oracle_alive": oracle_alive,
        "cheap_drop_count": cheap_drop_count,
        "accepted_count": len(result.accepted),
        "held_count": len(result.held),
        "rejected_count": len(result.rejected),
        "appended_ids": result.appended_ids,
        "error_kind": result.error_kind,
        "error": error,
    }
    LATEST_STATUS_PATH.write_text(
        json.dumps(record, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def _judge_candidates(
    *,
    codex_candidates: list[dict],
    oracle_candidates: list[dict],
) -> tuple[list[dict], list[dict], str]:
    """Run Codex judge prompt; returns (accepted, rejected, error)."""
    if not codex_candidates and not oracle_candidates:
        return ([], [], "")

    template = (PROMPTS_DIR / "board_judge.txt").read_text(encoding="utf-8")
    board_content = board_context.build_board_prompt_context()
    paper_coverage_blob = paper_index.render_prompt_summary(max_chars=12000)

    codex_blob = json.dumps(codex_candidates, ensure_ascii=False, indent=2)
    oracle_blob = json.dumps(oracle_candidates, ensure_ascii=False, indent=2)

    prompt = template.format(
        board_content=_safe(board_content),
        paper_coverage=_safe(paper_coverage_blob[:20000]),
        codex_candidates=_safe(codex_blob),
        oracle_candidates=_safe(oracle_blob),
    )
    log_tag = "board_judge"
    ok, parsed, stdout, error = _codex_json_fallback(
        prompt,
        timeout=DEFAULT_JUDGE_TIMEOUT,
        log_tag=log_tag,
        role_note=(
            "Run the BEDC BOARD spawn judge as the primary Codex gate. "
            "Use the prompt's maker/checker standard directly; there is no "
            "external pre-screen in this pipeline."
        ),
    )
    if not ok:
        return ([], [], f"codex judge failed: {error[:300]}")
    if not parsed:
        return ([], [], "codex judge output was not JSON")
    accepted = parsed.get("accepted_candidates") or []
    rejected = parsed.get("rejected_candidates") or []
    return (accepted if isinstance(accepted, list) else [],
            rejected if isinstance(rejected, list) else [],
            "")


# ---------------------------------------------------------------------------
# BOARD append
# ---------------------------------------------------------------------------


def _render_entry(target_id: str, candidate: dict) -> str:
    title = candidate.get("title", "(untitled)")
    claim = candidate.get("claim", "")
    chapter = candidate.get("chapter", "concrete_instances")
    fit = candidate.get("fit_score", "?")
    novelty = candidate.get("novelty", "?")
    source = candidate.get("source", "judge")
    landing_kind = str(candidate.get("landing_kind") or "existing_chapter_lemma").strip()
    chapter_worthiness = str(candidate.get("chapter_worthiness") or "").strip()
    rationale = candidate.get("rationale", "")
    inputs = candidate.get("local_inputs") or []
    inputs_block = "\n".join(f"- `{p}`" for p in inputs) if inputs else "- (auto-spawn — no specific inputs declared)"
    worthiness_block = f"\nChapter worthiness:\n{chapter_worthiness}\n" if chapter_worthiness else ""
    pretastegate_fields = [
        "tastegate_mode",
        *PRE_TASTEGATE_REQUIRED_FIELDS.keys(),
        *PRE_TASTEGATE_OPTIONAL_FIELDS[1:],
    ]
    pretastegate_lines = []
    for key in pretastegate_fields:
        value = str(candidate.get(key) or "").strip()
        if value:
            pretastegate_lines.append(f"- `{key}`: {value}")
    pretastegate_block = ""
    if pretastegate_lines:
        pretastegate_block = "\nPre-TasteGate admission:\n" + "\n".join(pretastegate_lines) + "\n"
    logic_lines = []
    for key in LOGIC_PACKET_FIELDS:
        value = str(candidate.get(key) or "").strip()
        if value:
            logic_lines.append(f"- `{key}`: {value}")
    logic_block = ""
    if logic_lines:
        logic_block = "\nLogic packet discipline:\n" + "\n".join(logic_lines) + "\n"
    return (
        f"\n### {target_id} - {title}\n\n"
        f"| field | value |\n"
        f"|---|---|\n"
        f"| Status | Candidate (auto-spawned) |\n"
        f"| Source | bedc-deep board_spawn ({source}) |\n"
        f"| Object | {title} |\n"
        f"| Layer | {chapter} |\n"
        f"| Route | proof |\n"
        f"| Risk | unknown |\n"
        f"| Fit | {fit}/10 |\n"
        f"| Novelty | {novelty}/10 |\n"
        f"| Landing kind | {landing_kind} |\n\n"
        f"Problem:\n{claim}\n\n"
        f"Local inputs:\n{inputs_block}\n\n"
        f"{worthiness_block}"
        f"{pretastegate_block}"
        f"{logic_block}"
        f"Rationale:\n{rationale}\n\n---\n"
    )


def _field_text(candidate: dict, key: str) -> str:
    value = candidate.get(key)
    if isinstance(value, list):
        return " ".join(str(v).strip() for v in value if str(v).strip())
    return str(value or "").strip()


def _is_conjecture_fallback(candidate: dict) -> bool:
    """Conjecture fallback is a review lane, not an executable BOARD lane."""
    tastegate_mode = _field_text(candidate, "tastegate_mode").lower()
    if tastegate_mode == "conjecture_fallback":
        return True
    value = _field_text(candidate, "conjecture_fallback").lower()
    if not value:
        return False
    if value in {"false", "no", "none", "n/a", "na", "0"}:
        return False
    return True


def _pre_tastegate_rejection(candidate: dict) -> str:
    """Hard admission gate for candidates trying to create a new chapter."""
    landing_kind = str(candidate.get("landing_kind") or "").strip()
    if landing_kind != "new_chapter":
        return ""
    missing: list[str] = []
    for key, (_label, min_len) in PRE_TASTEGATE_REQUIRED_FIELDS.items():
        value = _field_text(candidate, key)
        if len(value) < min_len:
            missing.append(key)
    if missing:
        return "new_chapter_missing_pretastegate:" + ",".join(missing)

    tastegate_mode = _field_text(candidate, "tastegate_mode").lower()
    if tastegate_mode and tastegate_mode not in {
        "chapter",
        "new_chapter",
        "chapter_candidate",
        "hard",
        "pre_tastegate",
        "pretastegate",
    }:
        return f"new_chapter_invalid_tastegate_mode:{tastegate_mode[:40]}"

    if _is_conjecture_fallback(candidate):
        return "new_chapter_should_route_to_conjecture_fallback"
    return ""


def _post_judge_landing_rejection(candidate: dict) -> str:
    if _is_conjecture_fallback(candidate):
        return "conjecture_fallback_not_board_lane"
    title = str(candidate.get("title") or "")
    claim = str(candidate.get("claim") or candidate.get("concrete_claim") or "")
    rationale = str(candidate.get("rationale") or "")
    worthiness = str(candidate.get("chapter_worthiness") or "")
    haystack = " ".join([title, claim, rationale, worthiness])
    if not EXTERNAL_SIGNAL_RE.search(haystack):
        return _pre_tastegate_rejection(candidate)
    landing_kind = str(candidate.get("landing_kind") or "").strip()
    if not landing_kind:
        return "external_signal_missing_landing_kind"
    if landing_kind not in LANDING_KINDS:
        return f"external_signal_invalid_landing_kind:{landing_kind}"
    if landing_kind == "reject":
        return "external_signal_landing_reject"
    if landing_kind == "new_chapter":
        required = ("carrier", "classifier", "NameCert", "dependency", "downstream", "existing chapter")
        if len(worthiness.strip()) < 240 or any(term.lower() not in worthiness.lower() for term in required):
            return "external_signal_missing_chapter_worthiness"
        pretastegate = _pre_tastegate_rejection(candidate)
        if pretastegate:
            return pretastegate
        return "external_signal_new_chapter_not_board_lane"
    return ""


def _logic_packet_rejection(candidate: dict) -> str:
    result = logic_packet_gate.validate_logic_packet(candidate)
    if result.ok:
        return ""
    return "logic_packet_gate:" + ";".join(result.reasons)


def _substance_rejection(candidate: dict) -> str:
    return candidate_substance.substance_rejection(candidate)


def _deterministic_fallback_rejection(
    candidate: dict,
    *,
    fit_threshold: int,
    novelty_threshold: int,
) -> str:
    """Conservative BOARD intake when the Codex judge is unavailable.

    This is deliberately narrower than the normal board_judge.  It only admits
    deterministic supply lanes whose packets already survived candidate_inbox,
    have BEDC-local landing files, complete logic metadata, and no obvious
    anti-parameter-echo shape.  New chapters and external-source packets still
    require the normal judge.
    """
    source = str(candidate.get("source") or "").strip()
    if source not in DETERMINISTIC_FALLBACK_SOURCES:
        return f"deterministic_fallback_source_requires_llm_judge:{source or 'unknown'}"
    landing_kind = str(candidate.get("landing_kind") or "").strip()
    if landing_kind not in DETERMINISTIC_ALLOWED_LANDING:
        return f"deterministic_fallback_landing_requires_llm_judge:{landing_kind or 'missing'}"
    text = " ".join(
        str(candidate.get(key) or "")
        for key in ("title", "claim", "concrete_claim", "rationale")
    )
    if EXTERNAL_SIGNAL_RE.search(text):
        return "deterministic_fallback_external_signal_requires_llm_judge"
    if ANTI_PARAMETER_ECHO_RE.search(text):
        return "deterministic_fallback_anti_parameter_echo"
    substance_rejection = _substance_rejection(candidate)
    if substance_rejection:
        return substance_rejection
    inputs = candidate.get("local_inputs") or []
    if not isinstance(inputs, list) or not inputs:
        return "deterministic_fallback_missing_local_inputs"
    for rel in inputs:
        rel = str(rel or "").strip()
        if not rel.startswith("papers/bedc/parts/"):
            return f"deterministic_fallback_non_paper_input:{rel}"
        if re.search(r"^papers/bedc/parts/(?:visions|conjectures)/", rel, re.I):
            return f"deterministic_fallback_inspiration_only_input:{rel}"
        if not (REPO_ROOT / rel).exists():
            return f"deterministic_fallback_missing_input:{rel}"
    landing_rejection = _post_judge_landing_rejection(candidate)
    if landing_rejection:
        return landing_rejection
    logic_rejection = _logic_packet_rejection(candidate)
    if logic_rejection:
        return logic_rejection
    try:
        int(candidate.get("fit_score", 0))
        int(candidate.get("novelty", 0))
    except (TypeError, ValueError):
        return "deterministic_fallback_non_int_score"
    return ""


def _deterministic_fallback_judge(
    candidates: list[dict],
    *,
    fit_threshold: int,
    novelty_threshold: int,
) -> tuple[list[dict], list[dict]]:
    accepted: list[dict] = []
    rejected: list[dict] = []
    for candidate in candidates:
        reason = _deterministic_fallback_rejection(
            candidate,
            fit_threshold=fit_threshold,
            novelty_threshold=novelty_threshold,
        )
        if reason:
            rejected.append({**candidate, "reason": reason})
            continue
        accepted.append(
            {
                **candidate,
                "source": str(candidate.get("source") or "deterministic_fallback"),
                "rationale": (
                    str(candidate.get("rationale") or "").strip()
                    + " Deterministic BOARD fallback admitted this only after "
                    "candidate_inbox, local-input, logic-packet, landing-kind, "
                    "and anti-parameter-echo gates; final writeback gates still apply."
                ).strip(),
            }
        )
    return accepted, rejected


def _direct_codex_rejection(candidate: dict) -> str:
    """Local BOARD admission for pre-screened codex-lane packets."""
    source = str(candidate.get("source") or "").strip()
    if source not in DIRECT_CODEX_SOURCES:
        return f"direct_codex_source_requires_judge:{source or 'unknown'}"
    landing_kind = str(candidate.get("landing_kind") or "").strip()
    if landing_kind not in DETERMINISTIC_ALLOWED_LANDING:
        return f"direct_codex_landing_requires_judge:{landing_kind or 'missing'}"
    landing_rejection = _post_judge_landing_rejection(candidate)
    if landing_rejection:
        return landing_rejection
    logic_rejection = _logic_packet_rejection(candidate)
    if logic_rejection:
        return logic_rejection
    text = " ".join(
        str(candidate.get(key) or "")
        for key in ("title", "claim", "concrete_claim", "rationale")
    )
    if ANTI_PARAMETER_ECHO_RE.search(text):
        return "direct_codex_anti_parameter_echo"
    substance_rejection = _substance_rejection(candidate)
    if substance_rejection:
        return substance_rejection
    try:
        int(candidate.get("fit_score", 0))
        int(candidate.get("novelty", 0))
    except (TypeError, ValueError):
        return "non_int_score"
    return ""


def _direct_codex_admission(candidates: list[dict]) -> tuple[list[dict], list[dict], list[dict]]:
    accepted: list[dict] = []
    held_or_rejected: list[dict] = []
    needs_judge: list[dict] = []
    for candidate in candidates:
        reason = _direct_codex_rejection(candidate)
        if not reason:
            accepted.append(
                {
                    **candidate,
                    "rationale": (
                        str(candidate.get("rationale") or "").strip()
                        + " Local BOARD admission used the deterministic "
                        "candidate inbox, landing, and logic-packet gates; "
                        "codex execution and writeback gates remain decisive."
                    ).strip(),
                }
            )
            continue
        if (
            reason.startswith("direct_codex_source_requires_judge:")
            or reason.startswith("direct_codex_landing_requires_judge:")
        ):
            needs_judge.append(candidate)
            continue
        held_or_rejected.append({**candidate, "reason": reason})
    return accepted, held_or_rejected, needs_judge


def _rejection_match_keys(candidate: dict) -> list[tuple[str, str]]:
    keys: list[tuple[str, str]] = []
    for field_name in ("candidate_id", "title"):
        value = str(candidate.get(field_name) or "").strip().lower()
        if value:
            keys.append((field_name, value))
    return keys


def _hydrate_judge_items(items: list[dict], originals: list[dict]) -> list[dict]:
    """Preserve original candidate packet fields on compact judge items.

    The judge often returns compact accepted/rejected items containing only
    title/source/reason. Later strict-out gates and inbox telemetry need the
    original claim, inputs, and logic-packet fields to remain visible.
    """
    if not items or not originals:
        return items
    by_key: dict[tuple[str, str], dict] = {}
    for candidate in originals:
        if not isinstance(candidate, dict):
            continue
        for key in _rejection_match_keys(candidate):
            by_key.setdefault(key, candidate)
    hydrated: list[dict] = []
    for item in items:
        if not isinstance(item, dict):
            continue
        original = None
        for key in _rejection_match_keys(item):
            original = by_key.get(key)
            if original:
                break
        if original:
            hydrated.append({**original, **item})
        else:
            hydrated.append(item)
    return hydrated


def _hydrate_judge_rejections(rejected: list[dict], originals: list[dict]) -> list[dict]:
    return _hydrate_judge_items(rejected, originals)


def _atomic_append_to_board(blocks: list[str]) -> None:
    if not blocks:
        return
    original = BOARD_PATH.read_text(encoding="utf-8").rstrip()
    new_text = original + "\n" + "\n".join(blocks) + "\n"
    tmp = BOARD_PATH.with_suffix(BOARD_PATH.suffix + ".tmp")
    tmp.write_text(new_text, encoding="utf-8")
    tmp.replace(BOARD_PATH)


# ---------------------------------------------------------------------------
# Public entry
# ---------------------------------------------------------------------------


def spawn_from_candidates(
    *,
    codex_candidates: list[dict],
    oracle_candidates: list[dict],
    fit_threshold: int = DEFAULT_FIT_THRESHOLD,
    novelty_threshold: int = DEFAULT_NOVELTY_THRESHOLD,
) -> BoardSpawnResult:
    """Run the BOARD spawn gate over combined candidate lists.

    Returns BoardSpawnResult with accepted/rejected/appended_ids.
    """
    codex_input = len(codex_candidates)
    oracle_input = len(oracle_candidates)
    if not codex_candidates and not oracle_candidates:
        return BoardSpawnResult(ok=True)

    # Step 1: runtime inbox + deterministic pre-gate. This keeps the active
    # BOARD as an execution queue instead of a proposal/memory sink.
    codex_screen = candidate_inbox.screen_candidates(
        codex_candidates,
        source="codex",
        fit_threshold=fit_threshold,
        novelty_threshold=novelty_threshold,
    )
    oracle_screen = candidate_inbox.screen_candidates(
        oracle_candidates,
        source="oracle",
        fit_threshold=fit_threshold,
        novelty_threshold=novelty_threshold,
    )
    codex_alive = codex_screen.accepted
    oracle_alive = oracle_screen.accepted
    cheap_holds = codex_screen.held + oracle_screen.held
    cheap_drops = codex_screen.rejected + oracle_screen.rejected

    if not codex_alive and not oracle_alive:
        print(
            f"[board_spawn] all {len(codex_candidates) + len(oracle_candidates)} "
            f"candidates stopped before judge",
            flush=True,
        )
        result = BoardSpawnResult(ok=True, held=cheap_holds, rejected=cheap_drops)
        candidate_inbox.record_rejections(cheap_drops + cheap_holds, mode="board_spawn")
        _write_latest_status(
            result=result,
            codex_input=codex_input,
            oracle_input=oracle_input,
            codex_alive=0,
            oracle_alive=0,
            cheap_drop_count=len(cheap_drops) + len(cheap_holds),
        )
        return result

    # Step 2: local admission for pre-screened codex candidates; judge only
    # packets whose source or landing shape still requires a second pass.
    direct_accepted, direct_stopped, codex_alive_for_judge = _direct_codex_admission(codex_alive)
    if direct_accepted:
        print(
            f"[board_spawn] direct codex admission accepted={len(direct_accepted)} "
            f"needs_judge={len(codex_alive_for_judge)}",
            flush=True,
        )
    if not codex_alive_for_judge and not oracle_alive:
        accepted = direct_accepted
        rejected = direct_stopped
        err = ""
    else:
        # Step 3: Codex judge (with source signals + paper coverage).
        print(
            f"[board_spawn] judging {len(codex_alive_for_judge)} codex + {len(oracle_alive)} oracle candidates",
            flush=True,
        )
        accepted, rejected, err = _judge_candidates(
            codex_candidates=codex_alive_for_judge,
            oracle_candidates=oracle_alive,
        )
        accepted = _hydrate_judge_items(accepted, codex_alive_for_judge + oracle_alive)
        accepted = direct_accepted + accepted
        rejected = _hydrate_judge_rejections(rejected, codex_alive_for_judge + oracle_alive)
        rejected = direct_stopped + rejected
    if err:
        error_kind = classify_judge_error(err)
        if error_kind.startswith("board_judge_unavailable"):
            accepted, deterministic_rejected = _deterministic_fallback_judge(
                codex_alive_for_judge + oracle_alive,
                fit_threshold=fit_threshold,
                novelty_threshold=novelty_threshold,
            )
            accepted = direct_accepted + accepted
            deterministic_rejected = direct_stopped + deterministic_rejected
            rejected = deterministic_rejected
            if accepted:
                print(
                    "[board_spawn] Codex judge unavailable; using conservative "
                    f"deterministic fallback accepted={len(accepted)} "
                    f"rejected={len(rejected)}",
                    flush=True,
                )
            else:
                result = BoardSpawnResult(
                    ok=True,
                    error=err,
                    error_kind=error_kind,
                    held=cheap_holds + deterministic_rejected,
                    rejected=cheap_drops,
                )
                _write_latest_status(
                    result=result,
                    codex_input=codex_input,
                    oracle_input=oracle_input,
                    codex_alive=len(codex_alive),
                    oracle_alive=len(oracle_alive),
                    cheap_drop_count=len(cheap_drops) + len(cheap_holds),
                )
                return result
        else:
            result = BoardSpawnResult(
                ok=False,
                error=err,
                error_kind=error_kind,
                held=cheap_holds,
                rejected=cheap_drops + rejected,
            )
            _write_latest_status(
                result=result,
                codex_input=codex_input,
                oracle_input=oracle_input,
                codex_alive=len(codex_alive),
                oracle_alive=len(oracle_alive),
                cheap_drop_count=len(cheap_drops) + len(cheap_holds),
            )
            return result

    if err and accepted:
        # The deterministic fallback path above has already populated accepted
        # and rejected.  Continue into the same defensive threshold/write path.
        pass
    elif err:
        result = BoardSpawnResult(
            ok=False,
            error=err,
            error_kind=classify_judge_error(err),
            held=cheap_holds,
            rejected=cheap_drops + rejected,
        )
        _write_latest_status(
            result=result,
            codex_input=codex_input,
            oracle_input=oracle_input,
            codex_alive=len(codex_alive),
            oracle_alive=len(oracle_alive),
            cheap_drop_count=len(cheap_drops) + len(cheap_holds),
        )
        return result

    # Step 3: enforce hard paper-boundary metadata only.
    #
    # Fit/novelty are ranking signals, not admission axioms.  Wide-in /
    # strict-out means a BEDC-local, logic-packet-complete candidate may enter
    # BOARD for codex execution even if its score is low; the later writeback
    # and build gates decide whether anything becomes paper.
    final_accepted: list[dict] = []
    threshold_drops: list[dict] = []
    for c in accepted:
        landing_rejection = _post_judge_landing_rejection(c)
        if landing_rejection:
            threshold_drops.append({**c, "reason": landing_rejection})
            continue
        logic_rejection = _logic_packet_rejection(c)
        if logic_rejection:
            threshold_drops.append({**c, "reason": logic_rejection})
            continue
        substance_rejection = _substance_rejection(c)
        if substance_rejection:
            threshold_drops.append({**c, "reason": substance_rejection})
            continue
        try:
            int(c.get("fit_score", 0))
            int(c.get("novelty", 0))
        except (TypeError, ValueError):
            threshold_drops.append({**c, "reason": "non_int_score"})
            continue
        final_accepted.append(c)

    # Step 4: atomic append under board lock.
    appended_ids: list[str] = []
    if final_accepted:
        with file_lock("board"):
            blocks: list[str] = []
            local_acc: list[str] = []
            for c in final_accepted:
                tid = _next_target_id(local_acc)
                blocks.append(_render_entry(tid, c))
                local_acc.append(tid)
                appended_ids.append(tid)
            _atomic_append_to_board(blocks)
            candidate_inbox.record_board_promotions(final_accepted, appended_ids, mode="board_spawn")

    post_judge_holds: list[dict] = []
    post_judge_rejects: list[dict] = []
    for item in rejected + threshold_drops:
        reason = str(item.get("reason") or item.get("verdict_reason") or "")
        if candidate_inbox.is_refinable_reason(reason):
            post_judge_holds.append(item)
        else:
            post_judge_rejects.append(item)
    all_held = cheap_holds + post_judge_holds
    all_rejected = cheap_drops + post_judge_rejects
    print(
        f"[board_spawn] accepted={len(final_accepted)} held={len(all_held)} rejected={len(all_rejected)}",
        flush=True,
    )
    candidate_inbox.record_rejections(all_held + all_rejected, mode="board_spawn")
    result = BoardSpawnResult(
        ok=True,
        accepted=final_accepted,
        held=all_held,
        rejected=all_rejected,
        appended_ids=appended_ids,
    )
    _write_latest_status(
        result=result,
        codex_input=codex_input,
        oracle_input=oracle_input,
        codex_alive=len(codex_alive),
        oracle_alive=len(oracle_alive),
        cheap_drop_count=len(cheap_drops),
    )
    return result


# ---------------------------------------------------------------------------
# Oracle adjacent self-report (Stage 1.6 — invoked after oracle declares done)
# ---------------------------------------------------------------------------


def build_oracle_adjacent_prompt(
    *,
    target_id: str,
    target_title: str,
    proven_results_summary: str = "",
) -> str:
    """Build the prompt that asks oracle to self-report adjacent BOARD candidates.

    This prompt goes to the oracle in the same conversation as a follow-up,
    AFTER oracle has reached its terminal proven state. Caller submits via
    submit_turn(.../continue), captures response, and parses out the JSON
    list to feed into spawn_from_candidates(oracle_candidates=...).
    """
    template = (PROMPTS_DIR / "oracle_adjacent.txt").read_text(encoding="utf-8")
    # Use last id placeholders. We don't know exactly how oracle numbered;
    # the prompt phrases #{N1}-#{Nk} loosely so oracle interprets correctly.
    return template.format(
        target_id=_safe(target_id),
        target_title=_safe(target_title),
        N1="N_first",
        Nk="N_last",
    )


def parse_oracle_adjacent_response(response: str) -> list[dict]:
    """Extract the candidate list from oracle's adjacent-direction self-report."""
    if not response or not response.strip():
        return []
    # Look for a JSON array of objects
    arr_match = re.search(r"\[\s*\{.*\}\s*\]", response, flags=re.DOTALL)
    if not arr_match:
        return []
    try:
        arr = json.loads(arr_match.group(0))
    except json.JSONDecodeError:
        return []
    if not isinstance(arr, list):
        return []
    out: list[dict] = []
    for item in arr:
        if not isinstance(item, dict):
            continue
        out.append({
            "title": str(item.get("title", "")).strip(),
            "claim": str(item.get("claim", "")).strip(),
            "chapter": str(item.get("chapter", "concrete_instances")).strip(),
            "relation": str(item.get("relation", "sibling")).strip(),
            "rationale": str(item.get("rationale", "")).strip(),
            "source": "oracle",
        })
    return [c for c in out if c["title"] and c["claim"]]


# ---------------------------------------------------------------------------
# CLI smoke test
# ---------------------------------------------------------------------------


def main() -> int:
    import argparse

    parser = argparse.ArgumentParser(description="board_spawn smoke test")
    parser.add_argument("--codex-json", default="",
                        help="path to JSON file with codex_candidates list")
    parser.add_argument("--oracle-json", default="",
                        help="path to JSON file with oracle_candidates list")
    parser.add_argument("--dry-run", action="store_true",
                        help="run judge but do not append to BOARD")
    args = parser.parse_args()

    codex = json.loads(Path(args.codex_json).read_text()) if args.codex_json else []
    oracle = json.loads(Path(args.oracle_json).read_text()) if args.oracle_json else []

    if args.dry_run:
        accepted, rejected, err = _judge_candidates(
            codex_candidates=codex, oracle_candidates=oracle
        )
        print(json.dumps({
            "judge_ok": not err,
            "error": err,
            "accepted": accepted,
            "rejected": rejected,
        }, indent=2, ensure_ascii=False))
        return 0
    result = spawn_from_candidates(
        codex_candidates=codex, oracle_candidates=oracle
    )
    print(json.dumps({
        "ok": result.ok,
        "appended_ids": result.appended_ids,
        "accepted_count": len(result.accepted),
        "rejected_count": len(result.rejected),
        "error": result.error,
        "error_kind": result.error_kind,
    }, indent=2, ensure_ascii=False))
    return 0 if result.ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
