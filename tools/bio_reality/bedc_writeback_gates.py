#!/usr/bin/env python3
"""Deterministic gates for BioReality BEDC writeback packets."""

from __future__ import annotations

import argparse
import json
import re
import sys
from typing import Any


THEOREM_ENV_RE = re.compile(
    r"\\begin\{(?:theorem|definition|lemma|proof|closurestatus)\}"
)
TOP_LEVEL_MATH_ENV_RE = re.compile(
    r"\\\[|\\begin\{(?:equation|align|eqnarray)\*?\}"
)
FOO_UP_TEXT_ARG_RE = re.compile(r"\{[^{}]*\\[A-Z]\w*Up[^{}]*\}", re.DOTALL)
EXTERNAL_BODY_RE = re.compile(
    r"(?:tools/[^\s{}]*\.(?:json|jsonl)|state/[^\s{}]*\.jsonl|"
    r"experiment_run_id|https?://|arxiv\.org|wikipedia\.org|"
    r"ChatGPT|GPT-|Anthropic|Claude|Codex)"
)
LEAN_MARKER_RE = re.compile(
    r"\\(?:leanstmt|leantarget|leanchecked|leanvariant|leandef|leansorryd)\{"
)
GENERIC_TEMPLATE_PHRASES = [
    "finite reality-bound seed witness for the claim",
    "finite, reality-bound seed witness for the claim",
    "finite reality-bound seed witness for claim",
]


def _nonblank_line_count(text: str) -> int:
    return sum(1 for line in text.splitlines() if line.strip())


def line_count_le_800(text: str) -> list[str]:
    count = _nonblank_line_count(text)
    if count > 800:
        return [f"file has {count} nonblank line(s), exceeds 800"]
    return []


def hub_line_count_le_15(hub_text: str) -> list[str]:
    count = _nonblank_line_count(hub_text)
    if count > 15:
        return [f"hub has {count} nonblank line(s), exceeds 15"]
    return []


def hub_has_no_theorem_env(hub_text: str) -> list[str]:
    match = THEOREM_ENV_RE.search(hub_text)
    if match is None:
        return []
    return [f"hub contains forbidden environment {match.group(0)}"]


def no_top_level_math_envs(text: str) -> list[str]:
    match = TOP_LEVEL_MATH_ENV_RE.search(text)
    if match is None:
        return []
    return [f"forbidden top-level math environment {match.group(0)}"]


def _remove_math_spans(text: str) -> str:
    out: list[str] = []
    index = 0
    in_math = False
    while index < len(text):
        if text.startswith("$$", index):
            out.append("  ")
            index += 2
            in_math = not in_math
            continue
        if text[index] == "$":
            out.append(" ")
            index += 1
            in_math = not in_math
            continue
        out.append(" " if in_math else text[index])
        index += 1
    return "".join(out)


def foo_up_in_text_mode(text: str) -> list[str]:
    issues: list[str] = []
    text_without_math = _remove_math_spans(text)
    for match in FOO_UP_TEXT_ARG_RE.finditer(text_without_math):
        prefix = text_without_math[max(0, match.start() - 32) : match.start()]
        if prefix.endswith(r"\begin{closurestatus}"):
            continue
        snippet = " ".join(match.group(0).split())
        issues.append(f"FooUp macro appears in text-mode argument without math wrapping: {snippet[:120]}")
    return issues


def no_external_path_in_body(text: str) -> list[str]:
    issues: list[str] = []
    for match in EXTERNAL_BODY_RE.finditer(text):
        issues.append(f"external path or generator identity leaked into BEDC body: {match.group(0)}")
    return issues


def _find_closurestatus_blocks(text: str) -> list[str]:
    blocks: list[str] = []
    begin_re = re.compile(r"\\begin\{closurestatus\}\{[^{}]*\}")
    end_token = r"\end{closurestatus}"
    for match in begin_re.finditer(text):
        end = text.find(end_token, match.end())
        if end == -1:
            blocks.append(text[match.start() :])
        else:
            blocks.append(text[match.start() : end + len(end_token)])
    return blocks


def _macro_has_nonempty_arg(block: str, macro: str) -> bool:
    match = re.search(rf"\\{re.escape(macro)}\{{", block)
    if match is None:
        return False
    depth = 1
    index = match.end()
    arg_start = index
    while index < len(block):
        char = block[index]
        if char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                return bool(block[arg_start:index].strip())
        index += 1
    return False


def closurestatus_complete(spine_text: str) -> list[str]:
    required = [
        "constructivestory",
        "theoryclosure",
        "scopeclosed",
        "formalstatus",
        "bridgestatus",
        "notclaimed",
        "upgradepath",
    ]
    blocks = _find_closurestatus_blocks(spine_text)
    if not blocks:
        return ["spine is missing closurestatus block"]
    issues: list[str] = []
    for block_index, block in enumerate(blocks, 1):
        for macro in required:
            if not _macro_has_nonempty_arg(block, macro):
                issues.append(f"closurestatus block {block_index} missing nonempty \\{macro}{{...}}")
    return issues


def origin_ai_has_falsifiable_and_independence(spine_text: str) -> list[str]:
    if r"\origin{ai}" not in spine_text:
        return []
    issues: list[str] = []
    if r"\falsifiablePrediction{" not in spine_text:
        issues.append(r"\origin{ai} spine missing \falsifiablePrediction{...}")
    if r"\independenceWitness{" not in spine_text:
        issues.append(r"\origin{ai} spine missing \independenceWitness{...}")
    return issues


def no_naked_leanstmt(text: str) -> list[str]:
    if LEAN_MARKER_RE.search(text):
        return ["lean marker present but lean target not registered; either add Lean target or remove marker"]
    return []


def generic_prose_detector(text: str, used_fact_ids: list[str] | None, min_used_fact_ids: int = 3) -> list[str]:
    issues: list[str] = []
    fact_count = len([item for item in (used_fact_ids or []) if isinstance(item, str) and item.strip()])
    if fact_count < min_used_fact_ids:
        issues.append(f"chapter does not consume enough verified_facts; got {fact_count}, required {min_used_fact_ids}")
    lowered = re.sub(r"\s+", " ", text.lower())
    for phrase in GENERIC_TEMPLATE_PHRASES:
        if phrase in lowered:
            issues.append(f"generic template phrase detected: {phrase}")
    if len(text.strip()) < 1500:
        issues.append("spine too thin to constitute a NameCert packet")
    return issues


def validate_hub_text(text: str) -> list[str]:
    issues: list[str] = []
    issues.extend(line_count_le_800(text))
    issues.extend(hub_line_count_le_15(text))
    issues.extend(hub_has_no_theorem_env(text))
    issues.extend(no_top_level_math_envs(text))
    issues.extend(foo_up_in_text_mode(text))
    issues.extend(no_external_path_in_body(text))
    issues.extend(no_naked_leanstmt(text))
    return issues


def validate_spine_text(text: str) -> list[str]:
    issues: list[str] = []
    issues.extend(line_count_le_800(text))
    issues.extend(no_top_level_math_envs(text))
    issues.extend(foo_up_in_text_mode(text))
    issues.extend(no_external_path_in_body(text))
    issues.extend(closurestatus_complete(text))
    issues.extend(origin_ai_has_falsifiable_and_independence(text))
    issues.extend(no_naked_leanstmt(text))
    return issues


def validate_chapter_pair(
    hub_text: str,
    spine_text: str,
    used_fact_ids: list[str] | None = None,
    min_used_fact_ids: int = 0,
) -> dict[str, Any]:
    hub_issues = [f"hub: {issue}" for issue in validate_hub_text(hub_text)]
    spine_issues = [f"spine: {issue}" for issue in validate_spine_text(spine_text)]
    generic_issues: list[str] = []
    if used_fact_ids is not None or min_used_fact_ids > 0:
        generic_issues = [
            f"spine: {issue}"
            for issue in generic_prose_detector(spine_text, used_fact_ids, min_used_fact_ids=min_used_fact_ids)
        ]
    issues = hub_issues + spine_issues + generic_issues
    return {
        "passed": not issues,
        "issues": issues,
        "hub_lines": _nonblank_line_count(hub_text),
        "spine_lines": _nonblank_line_count(spine_text),
    }


def _valid_hub() -> str:
    return "\n".join(
        [
            "% Auto-generated BioReality NameCert hub for h0.test.",
            "% This hub follows the newmath concrete-instances hub+subdir layout.",
            "% Only orienting prose and \\input lines are allowed here.",
            r"\input{parts/concrete_instances/bioreality_test/namecert_construction}",
            "",
        ]
    )


def _valid_spine() -> str:
    return "\n".join(
        [
            r"\chapter{A Concrete Naming Certificate for $\BioRealityTestUp$}",
            r"\label{ch:concrete-instances-bioreality-test-namecert}",
            r"\origin{ai}",
            "",
            "This BioReality NameCert packet records a bounded code-layer naming certificate. "
            "The packet is intentionally narrow: it keeps a curated code-row contact outside the BEDC kernel while recording only the internal naming surface needed for a finite coordinate reading. "
            "The text mentions three concrete fixture observations: 64 codon coordinates, 3 stop labels, and 1 carrier name reserved for this test packet. "
            "Those quantities are not treated as biochemical mechanisms; they are finite audit data for a name certificate that remains at the code-read layer. "
            "A second fixture sentence records that the carrier has 2 bookkeeping roles, coordinate display and closure bookkeeping, and that 0 claims about folding or function are made. "
            "A third fixture sentence records 5 excluded promotions: translation, folding, physical admissibility, function, and universality. "
            "Together these sentences make the packet thick enough for the writeback gate while preserving the self-contained boundary required of a concrete instance chapter.",
            "",
            r"\paragraph{Carrier.} $\BioRealityTestUp$ is the BEDC packet name.",
            "",
            r"\falsifiablePrediction{A $\BioRealityTestUp$ packet cannot export translation without a separate contact.}",
            "",
            r"\independenceWitness{The carrier records only coordinate and closure bookkeeping.}",
            "",
            r"\closureat{BioRealityTestUp}{seedStr}",
            r"\begin{closurestatus}{\BioRealityTestUp}",
            r"  \constructivestory{Finite seed witness for h0.test.}",
            r"  \theoryclosure{\seedClosure}",
            r"  \scopeclosed{Code-layer readback only.}",
            r"  \formalstatus{\unformalizedV}",
            r"  \bridgestatus{paperBridge}",
            r"  \notclaimed{No translation, folding, function, mechanism, or universality claim.}",
            r"  \upgradepath{Attach a separate reality contact.}",
            r"\end{closurestatus}",
            "",
        ]
    )


def self_test() -> int:
    checks: list[tuple[str, bool, Any]] = [
        ("line_count_le_800", bool(line_count_le_800("\n".join(["x"] * 801))), None),
        ("hub_line_count_le_15", bool(hub_line_count_le_15("\n".join(["x"] * 16))), None),
        ("hub_has_no_theorem_env", bool(hub_has_no_theorem_env(r"\begin{theorem}X\end{theorem}")), None),
        ("no_top_level_math_envs", bool(no_top_level_math_envs(r"\[x=y\]")), None),
        ("foo_up_in_text_mode", bool(foo_up_in_text_mode(r"\falsifiablePrediction{bad \FooUp text}")), None),
        ("no_external_path_in_body", bool(no_external_path_in_body("see tools/bio_reality/out/foo.json")), None),
        ("closurestatus_complete", bool(closurestatus_complete(r"\begin{closurestatus}{\FooUp}\formalstatus{}\end{closurestatus}")), None),
        ("origin_ai_has_falsifiable_and_independence", bool(origin_ai_has_falsifiable_and_independence(r"\origin{ai}")), None),
        ("no_naked_leanstmt", bool(no_naked_leanstmt(r"\leanstmt{BEDC.X}")), None),
        (
            "generic_prose_detector_phrase",
            bool(generic_prose_detector("A finite reality-bound seed witness for the claim appears here." + "x" * 1500, ["a", "b", "c"])),
            None,
        ),
        (
            "generic_prose_detector_pass",
            not generic_prose_detector(
                "This grounded packet cites 64 codons, row count 13, lambda 0.675248, and p-value 0.031. "
                + "The carrier stays at code-read scope and blocks translation promotion. " * 30,
                ["codon_count", "row_count", "lambda_M"],
            ),
            None,
        ),
    ]
    for name, ok, detail in checks:
        if not ok:
            print(json.dumps({"failed": name, "detail": detail}, indent=2), file=sys.stderr)
            return 1

    valid = validate_chapter_pair(_valid_hub(), _valid_spine())
    if not valid["passed"]:
        print(json.dumps(valid, indent=2), file=sys.stderr)
        return 1

    invalid = validate_chapter_pair(
        "\n".join(["x"] * 16) + "\n" + r"\begin{lemma}Bad\end{lemma}",
        r"\origin{ai}" + "\n" + r"\begin{align}x=y\end{align}" + "\n" + r"\leanstmt{BEDC.X}",
    )
    if invalid["passed"] or len(invalid["issues"]) < 5:
        print(json.dumps(invalid, indent=2), file=sys.stderr)
        return 1

    print("[bedc-writeback-gates] self-test ok")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run BioReality BEDC writeback gate self-test")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(argv)
    if args.self_test:
        return self_test()
    parser.print_help()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
