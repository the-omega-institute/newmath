#!/usr/bin/env python3
from __future__ import annotations

import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MAX_TEX_LINES = 800
SOURCE_ROOTS = (ROOT / "parts",)
TEXT_MACROS = ("falsifiablePrediction", "independenceWitness")
LEAN_MARKER_MACROS = ("leanchecked", "leanvariant", "leansorryd", "leanstmt", "leandef", "leantarget")
FORBIDDEN_MATH_PATTERNS = (
    re.compile(r"\\begin\{align\*?\}"),
    re.compile(r"\\end\{align\*?\}"),
    re.compile(r"\\begin\{eqnarray\*?\}"),
    re.compile(r"\\end\{eqnarray\*?\}"),
    re.compile(r"\\begin\{equation\*?\}"),
    re.compile(r"\\end\{equation\*?\}"),
    re.compile(r"(?<!\\)\\\["),
    re.compile(r"(?<!\\)\\\]"),
)
UP_DEFINITION_RE = re.compile(r"\\(?:providecommand|newcommand|renewcommand)\*?\s*\{\s*\\([A-Za-z][A-Za-z0-9]*Up)\s*\}")
COMMAND_DEFINITION_RE = re.compile(r"\\(?:providecommand|newcommand|renewcommand)\*?\s*\{\s*\\([A-Za-z][A-Za-z0-9]*)\s*\}")
UP_USE_RE = re.compile(r"\\([A-Z][A-Za-z0-9]*Up)\b")
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
REF_RE = re.compile(r"\\(?:autoref|ref|eqref|pageref)\{([^}]+)\}")
CITE_RE = re.compile(r"\\cite\{([^}]+)\}")
BIBITEM_RE = re.compile(r"\\bibitem\{([^}]+)\}")
BEGIN_ENV_RE = re.compile(r"\\begin\{([^}]+)\}")
END_ENV_RE = re.compile(r"\\end\{([^}]+)\}")

FORBIDDEN_NARRATIVE = (
    ("新增", None),
    ("新版", None),
    ("修订", None),
    ("修复了上一版本", None),
    ("增量", None),
    ("修改记录", None),
    ("变更记录", None),
    ("变更原因", None),
    ("newly added", re.compile(r"\bnewly\s+added\b", re.IGNORECASE)),
    ("newly", re.compile(r"\bnewly\b", re.IGNORECASE)),
    ("added", re.compile(r"\badded\b", re.IGNORECASE)),
    ("previous", re.compile(r"\bprevious(?:ly)?\b", re.IGNORECASE)),
    ("patch", re.compile(r"\bpatch\b", re.IGNORECASE)),
    ("migration", re.compile(r"\bmigration\b", re.IGNORECASE)),
    ("supersede", re.compile(r"\bsupersed(?:e|ed|es|ing)\b", re.IGNORECASE)),
    ("deprecated", re.compile(r"\bdeprecated\b", re.IGNORECASE)),
    ("updated", re.compile(r"\bupdated\b", re.IGNORECASE)),
    ("revised", re.compile(r"\brevised\b", re.IGNORECASE)),
    ("legacy", re.compile(r"\blegacy\b", re.IGNORECASE)),
    ("increment", re.compile(r"\bincrement(?:al|s|ed|ing)?\b", re.IGNORECASE)),
    ("rectification", re.compile(r"\brectification\b", re.IGNORECASE)),
    ("amendment", re.compile(r"\bamendment\b", re.IGNORECASE)),
    ("version", re.compile(r"\bversion\b", re.IGNORECASE)),
    ("v-tag", re.compile(r"\bv[0-9]+(?:\.[0-9A-Za-z]+|-[A-Za-z0-9])", re.IGNORECASE)),
)
FROZEN_ALLOWED_RE = re.compile(
    r"\bfrozen\s+(?:checkpoint|checkpoints|probe|probes|representation|representations|"
    r"ledger|ledgers|latent|latents|logit|logits|head|heads|\$g\$|E)\b",
    re.IGNORECASE,
)
FROZEN_RE = re.compile(r"\bfrozen\b", re.IGNORECASE)

GAP_READBACK_RE = re.compile(
    r"\b(?:gap\s*(?:head|heads|auc|auroc)|gap[- ]?AUC|gap[- ]?AUROC|"
    r"gap[- ]?readback|failure[- ]?readback|post-hoc\s+gap|"
    r"horizon[- ]?failure|horizon[- ]?ledger)\b",
    re.IGNORECASE,
)
CAPABILITY_PROMOTION_RE = re.compile(
    r"\b(?:architecture(?:-|\s+)?(?:level|capability|advantage)|"
    r"capability|superiority|outperform|beats?|wins?|win\s+rate|"
    r"planning\s+(?:success|benefit|improvement|advantage)|"
    r"control\s+(?:success|benefit|improvement|advantage)|"
    r"allocation\s+(?:success|benefit|improvement|advantage)|"
    r"public\s+benchmark\s+superiority)\b",
    re.IGNORECASE,
)
SAFE_GAP_BOUNDARY_RE = re.compile(
    r"\b(?:diagnostic|readback|predicate[- ]discovery|fixed[- ]scope|"
    r"bounded|scoped|not\s+(?:a|an|the|by|establish|established|claimed|claim|"
    r"promote|promoted)|does\s+not|do\s+not|cannot|fail[- ]closed|"
    r"no\s+(?:planning|control|allocation|public|architecture|capability|"
    r"superiority)|tradeoff|confidence\s+on|declared\s+failure[- ]readback)\b",
    re.IGNORECASE,
)
CLAIM_SURFACE_RE = re.compile(
    r"\\(?:title|section|subsection|subsubsection|paragraph|caption)\b|"
    r"\\begin\{abstract\}|\\end\{abstract\}",
    re.IGNORECASE,
)
GAP_RESULT_RE = re.compile(
    r"\b(?:gap\s*(?:auc|auroc)|gap[- ]?AUC|gap[- ]?AUROC|"
    r"failure[- ]?readback|gap[- ]?readback)\b",
    re.IGNORECASE,
)
PROMOTIONAL_ENDPOINT_RE = re.compile(
    r"\b(?:capability|world[- ]model|architecture[- ]level|superiority|"
    r"planning|control|allocation|benchmark\s+superiority|"
    r"improves?|improvement|beats?|wins?|outperform|positive\s+result)\b",
    re.IGNORECASE,
)
MECHANISM_TARGET_RE = re.compile(
    r"\b(?:mechanism[- ]aware\s+target|mechanism[- ]aware\s+assignment\s+target|"
    r"mechanism[- ]forced[- ]delta|oracle[- ]derived\s+target|"
    r"target\s+audit|target\s+ceiling|forced[- ]option\s+mechanism\s+labels)\b",
    re.IGNORECASE,
)
DEPLOYABLE_PROMOTION_RE = re.compile(
    r"\b(?:deployable\s+(?:policy|score|learner|allocation)|"
    r"allocation[- ]closed\s+(?:policy|control|learner)|"
    r"complete\s+BEDC[- ]native\s+world\s+model|"
    r"BEDC[- ]native\s+world[- ]model\s+capability|"
    r"learned\s+(?:policy|allocation\s+policy|control\s+policy))\b",
    re.IGNORECASE,
)
SAFE_MECHANISM_BOUNDARY_RE = re.compile(
    r"\b(?:target\s+audit|oracle[- ]derived|not\s+(?:a|an|the)?\s*deployable|"
    r"not\s+(?:a|an|the)?\s*allocation[- ]closed|not\s+(?:a|an|the)?\s*complete|"
    r"does\s+not\s+(?:close|supply|establish|promote)|cannot|fail[- ]closed|"
    r"next\s+closure\s+step|non[- ]leaky\s+predictor|independent\s+export)\b",
    re.IGNORECASE,
)

AI_NAMES = ("ChatGPT", "Claude", "OpenAI", "Anthropic")
ABS_PATH_MARKERS = ("/Users/", "/private/", "/tmp/", "/var/", "/opt/", "/home/", "C:\\")
EXTERNAL_NEEDLES = (
    "http://",
    "https://",
    "github.com",
    "GitHub.com",
    "Wikipedia",
    "wikipedia",
    "automath",
    "Automath",
    "review_packets",
)


def tex_files() -> list[Path]:
    files: list[Path] = [ROOT / "main.tex"]
    for root in SOURCE_ROOTS:
        if root.exists():
            files.extend(sorted(root.rglob("*.tex")))
    return [path for path in files if path.exists()]


def rel(path: Path) -> str:
    return str(path.relative_to(ROOT)).replace("\\", "/")


def strip_comments(text: str) -> str:
    out: list[str] = []
    for line in text.splitlines(keepends=True):
        escaped = False
        kept: list[str] = []
        for char in line:
            if char == "%" and not escaped:
                break
            kept.append(char)
            escaped = char == "\\" and not escaped
            if char != "\\":
                escaped = False
        out.append("".join(kept))
    return "".join(out)


def matching_brace(text: str, open_index: int) -> int | None:
    depth = 0
    escaped = False
    for index in range(open_index, len(text)):
        char = text[index]
        if escaped:
            escaped = False
            continue
        if char == "\\":
            escaped = True
            continue
        if char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                return index
    return None


def has_bare_underscore(text: str) -> bool:
    escaped = False
    in_math = False
    for char in text:
        if escaped:
            escaped = False
            continue
        if char == "\\":
            escaped = True
            continue
        if char == "$":
            in_math = not in_math
            continue
        if not in_math and char == "_":
            return True
    return False


def check_tex_size(files: list[Path]) -> list[str]:
    errors = []
    for path in files:
        if path.name == "main.tex":
            continue
        count = len(path.read_text(encoding="utf-8", errors="ignore").splitlines())
        if count > MAX_TEX_LINES:
            errors.append(f"{rel(path)}: {count} lines exceeds cap {MAX_TEX_LINES}")
    return errors


def check_math_env(files: list[Path]) -> list[str]:
    errors = []
    for path in files:
        text = path.read_text(encoding="utf-8", errors="ignore")
        for line_no, line in enumerate(text.splitlines(), 1):
            if line.lstrip().startswith("%"):
                continue
            for pattern in FORBIDDEN_MATH_PATTERNS:
                if pattern.search(line):
                    errors.append(f"{rel(path)}:{line_no}: forbidden top-level math env: {line.strip()[:120]}")
                    break
    return errors


def check_text_macro_underscores(files: list[Path]) -> list[str]:
    errors = []
    for path in files:
        text = path.read_text(encoding="utf-8", errors="ignore")
        for macro in (*TEXT_MACROS, *LEAN_MARKER_MACROS):
            needle = "\\" + macro + "{"
            start = 0
            while True:
                pos = text.find(needle, start)
                if pos < 0:
                    break
                open_index = pos + len(needle) - 1
                close_index = matching_brace(text, open_index)
                if close_index is None:
                    start = open_index + 1
                    continue
                body = text[open_index + 1 : close_index]
                if has_bare_underscore(body):
                    line_no = text.count("\n", 0, pos) + 1
                    errors.append(f"{rel(path)}:{line_no}: bare underscore inside \\{macro}{{...}}")
                start = close_index + 1
    return errors


def check_up_macros(files: list[Path]) -> list[str]:
    errors = []
    texts = {path: strip_comments(path.read_text(encoding="utf-8", errors="ignore")) for path in files}
    defined: set[str] = set()
    for text in texts.values():
        defined.update(match.group(1) for match in UP_DEFINITION_RE.finditer(text))
    for path, text in texts.items():
        for match in COMMAND_DEFINITION_RE.finditer(text):
            name = match.group(1)
            if any(char.isdigit() for char in name):
                line_no = text.count("\n", 0, match.start()) + 1
                errors.append(f"{rel(path)}:{line_no}: macro name '\\{name}' contains digits")
        for match in UP_USE_RE.finditer(text):
            name = match.group(1)
            if name not in defined:
                line_no = text.count("\n", 0, match.start()) + 1
                errors.append(f"{rel(path)}:{line_no}: undefined \\{name}")
    return errors


def check_external_provenance(files: list[Path]) -> list[str]:
    errors = []
    for path in files:
        if path.name == "main.tex":
            continue
        for line_no, line in enumerate(path.read_text(encoding="utf-8", errors="ignore").splitlines(), 1):
            stripped = line.strip()
            if not stripped or stripped.startswith("%"):
                continue
            if any(needle in line for needle in EXTERNAL_NEEDLES) or any(name in line for name in AI_NAMES):
                errors.append(f"{rel(path)}:{line_no}: external prose provenance leaked: {stripped[:180]}")
            if any(marker in line for marker in ABS_PATH_MARKERS):
                errors.append(f"{rel(path)}:{line_no}: absolute local path leaked: {stripped[:180]}")
    return errors


def check_no_iteration_narrative(files: list[Path]) -> list[str]:
    errors = []
    for path in files:
        for line_no, line in enumerate(path.read_text(encoding="utf-8", errors="ignore").splitlines(), 1):
            if line.lstrip().startswith("%"):
                continue
            for label, pattern in FORBIDDEN_NARRATIVE:
                hit = label in line if pattern is None else bool(pattern.search(line))
                if hit:
                    errors.append(f"{rel(path)}:{line_no}: forbidden current-state wording '{label}': {line.strip()[:160]}")
                    break
            else:
                stripped_frozen_contexts = FROZEN_ALLOWED_RE.sub("", line)
                if FROZEN_RE.search(stripped_frozen_contexts):
                    errors.append(f"{rel(path)}:{line_no}: forbidden current-state wording 'frozen': {line.strip()[:160]}")
    return errors


def check_gap_readback_claim_boundary(files: list[Path]) -> list[str]:
    errors = []
    for path in files:
        text = path.read_text(encoding="utf-8", errors="ignore")
        paragraphs = re.split(r"\n\s*\n", text)
        line_base = 1
        for paragraph in paragraphs:
            clean = " ".join(
                line.strip()
                for line in paragraph.splitlines()
                if line.strip() and not line.lstrip().startswith("%")
            )
            if clean and GAP_READBACK_RE.search(clean) and CAPABILITY_PROMOTION_RE.search(clean):
                if not SAFE_GAP_BOUNDARY_RE.search(clean):
                    errors.append(
                        f"{rel(path)}:{line_base}: gap readback appears promoted beyond "
                        f"diagnostic scope: {clean[:180]}"
                    )
            line_base += paragraph.count("\n") + 2
    return errors


def claim_surfaces(path: Path, text: str) -> list[tuple[int, str]]:
    surfaces: list[tuple[int, str]] = []
    lines = text.splitlines()
    in_abstract = False
    abstract_start = 1
    abstract_lines: list[str] = []
    for line_no, line in enumerate(lines, 1):
        if "\\begin{abstract}" in line:
            in_abstract = True
            abstract_start = line_no
            abstract_lines = []
            continue
        if "\\end{abstract}" in line:
            surfaces.append((abstract_start, " ".join(abstract_lines)))
            in_abstract = False
            abstract_lines = []
            continue
        if in_abstract:
            abstract_lines.append(line.strip())
        if CLAIM_SURFACE_RE.search(line):
            surfaces.append((line_no, line.strip()))

    paragraphs = re.split(r"\n\s*\n", text)
    line_base = 1
    for paragraph in paragraphs:
        clean = " ".join(
            line.strip()
            for line in paragraph.splitlines()
            if line.strip() and not line.lstrip().startswith("%")
        )
        if re.search(r"\\paragraph\{(?:Current result|Recorded measurements|Secondary outcomes)\}", clean):
            surfaces.append((line_base, clean))
        line_base += paragraph.count("\n") + 2
    return surfaces


def check_gap_auc_claim_surfaces(files: list[Path]) -> list[str]:
    errors = []
    for path in files:
        text = path.read_text(encoding="utf-8", errors="ignore")
        for line_no, surface in claim_surfaces(path, text):
            clean = re.sub(r"\s+", " ", surface)
            if GAP_RESULT_RE.search(clean) and PROMOTIONAL_ENDPOINT_RE.search(clean):
                if not SAFE_GAP_BOUNDARY_RE.search(clean):
                    errors.append(
                        f"{rel(path)}:{line_no}: gap-AUROC/readback claim surface lacks "
                        f"diagnostic or cannot-claim boundary: {clean[:180]}"
                    )
    return errors


def check_references(files: list[Path]) -> list[str]:
    text_by_path = {path: strip_comments(path.read_text(encoding="utf-8", errors="ignore")) for path in files}
    all_text = "\n".join(text_by_path.values())
    labels = set(LABEL_RE.findall(all_text))
    bibitems = set(BIBITEM_RE.findall(all_text))
    errors = []
    for path, text in text_by_path.items():
        for match in REF_RE.finditer(text):
            target = match.group(1)
            if target not in labels:
                line_no = text.count("\n", 0, match.start()) + 1
                errors.append(f"{rel(path)}:{line_no}: undefined reference {{{target}}}")
        for match in CITE_RE.finditer(text):
            for target in (item.strip() for item in match.group(1).split(",")):
                if target and target not in bibitems:
                    line_no = text.count("\n", 0, match.start()) + 1
                    errors.append(f"{rel(path)}:{line_no}: undefined citation {{{target}}}")
    return errors


def check_env_balance(files: list[Path]) -> list[str]:
    errors = []
    for path in files:
        stack: list[tuple[str, int]] = []
        text = strip_comments(path.read_text(encoding="utf-8", errors="ignore"))
        for line_no, line in enumerate(text.splitlines(), 1):
            for match in BEGIN_ENV_RE.finditer(line):
                stack.append((match.group(1), line_no))
            for match in END_ENV_RE.finditer(line):
                env = match.group(1)
                if not stack:
                    errors.append(f"{rel(path)}:{line_no}: unmatched \\end{{{env}}}")
                    continue
                top, top_line = stack.pop()
                if top != env:
                    errors.append(f"{rel(path)}:{line_no}: \\end{{{env}}} closes \\begin{{{top}}} from line {top_line}")
        for env, line_no in stack:
            errors.append(f"{rel(path)}:{line_no}: unmatched \\begin{{{env}}}")
    return errors


def check_lewm_evidence_pointer(files: list[Path]) -> list[str]:
    path = ROOT / "parts" / "lewm_instantiation.tex"
    if not path.exists():
        return []
    text = path.read_text(encoding="utf-8", errors="ignore")
    errors = []
    if "Record pointers" not in text:
        errors.append("parts/lewm_instantiation.tex: missing Record pointers section")
    normalized = text.replace("\\_", "_")
    if "not_claimed" not in normalized:
        errors.append("parts/lewm_instantiation.tex: missing explicit not_claimed pointer")
    required = (
        ("reports/lewm\\_gap\\_ledger\\_head\\_large.json", "reports/lewm_gap_ledger_head_large.json"),
        ("reports/lewm\\_native\\_vs\\_posthoc\\_paired.json", "reports/lewm_native_vs_posthoc_paired.json"),
        ("reports/lewm\\_allocation\\_information\\_bound.json", "reports/lewm_allocation_information_bound.json"),
        ("reports/lewm\\_d\\_ledger\\_shaped\\_reencoder.json", "reports/lewm_d_ledger_shaped_reencoder.json"),
        ("reports/lewm\\_pusht\\_independent\\_export.json", "reports/lewm_pusht_independent_export.json"),
    )
    for escaped, path in required:
        if escaped not in text and path not in text:
            errors.append(f"parts/lewm_instantiation.tex: missing evidence pointer {path}")
    return errors


def check_capability_promotion_contract(files: list[Path]) -> list[str]:
    text = "\n".join(path.read_text(encoding="utf-8", errors="ignore") for path in files)
    normalized = re.sub(r"\s+", " ", text.lower())
    required = (
        ("gap AUROC diagnostic boundary", r"gap\s+auroc.*diagnostic|diagnostic.*gap\s+auroc"),
        ("information-starved baseline boundary", r"information-starved"),
        ("fair or matched baseline", r"fair\s+baselines?|matched\s+(?:head|supervision|control|baseline)"),
        ("prediction parity gate", r"prediction\s+parity"),
        ("failure probability is not compute value", r"failure\s+probability\s+is\s+not\s+compute\s+value"),
        ("option-conditioned marginal value", r"option-conditioned\s+marginal\s+value"),
        ("exact-budget allocation gate", r"exact-budget\s+allocation"),
        ("nonleaky feature contract", r"nonleaky|label-defining\s+future\s+residual"),
    )
    errors = []
    for label, pattern in required:
        if not re.search(pattern, normalized):
            errors.append(f"missing capability-promotion contract term: {label}")
    return errors


def check_mechanism_target_claim_boundary(files: list[Path]) -> list[str]:
    errors = []
    text = "\n".join(path.read_text(encoding="utf-8", errors="ignore") for path in files)
    normalized = re.sub(r"\s+", " ", text.lower())
    required = (
        ("mechanism target is identified as a target audit", r"target\s+audit"),
        ("mechanism target is scoped as oracle-derived", r"oracle-derived"),
        ("next step requires a non-leaky predictor", r"non-leaky\s+predictor"),
        ("independent export validation remains required", r"independent\s+export"),
        ("fi-090 claim grade", r"fi-090.*target\s+ceiling.*oracle\s+audit.*not\s+deployable"),
        ("fi-091 claim grade", r"fi-091.*non-leaky\s+learner\s+partial.*not\s+all-budget\s+closed"),
        ("fi-099 claim grade", r"fi-099.*state-generation\s+fail-closed"),
    )
    for label, pattern in required:
        if not re.search(pattern, normalized):
            errors.append(f"missing mechanism-target boundary term: {label}")

    for path in files:
        file_text = path.read_text(encoding="utf-8", errors="ignore")
        paragraphs = re.split(r"\n\s*\n", file_text)
        line_base = 1
        for paragraph in paragraphs:
            clean = " ".join(
                line.strip()
                for line in paragraph.splitlines()
                if line.strip() and not line.lstrip().startswith("%")
            )
            if (
                clean
                and MECHANISM_TARGET_RE.search(clean)
                and DEPLOYABLE_PROMOTION_RE.search(clean)
                and not SAFE_MECHANISM_BOUNDARY_RE.search(clean)
            ):
                errors.append(
                    f"{rel(path)}:{line_base}: mechanism target appears promoted "
                    f"beyond target-audit scope: {clean[:180]}"
                )
            line_base += paragraph.count("\n") + 2
    return errors


def check_not_applicable_markers(files: list[Path]) -> list[str]:
    all_text = "\n".join(path.read_text(encoding="utf-8", errors="ignore") for path in files)
    markers = [macro for macro in LEAN_MARKER_MACROS if "\\" + macro + "{" in all_text]
    errors = []
    if markers:
        errors.append(f"Lean marker axis is not applicable for bedc_jepa, but markers are present: {', '.join(markers)}")
    return errors


def check_closurestatus(files: list[Path]) -> list[str]:
    all_text = "\n".join(path.read_text(encoding="utf-8", errors="ignore") for path in files)
    closures = "\\begin{closurestatus}" in all_text or "\\end{closurestatus}" in all_text
    errors = []
    if closures:
        errors.append("closurestatus axis is not applicable for bedc_jepa, but closurestatus blocks are present")
    return errors


def check_evidence_files_exist(files: list[Path]) -> list[str]:
    """Every ``\\path{...}`` pointer in the LeWM section that names an in-repo
    artifact (``experiments/...`` or ``formal/...``) must resolve to a real file
    or directory under the article root. This closes the gap where a pointer
    string is present in the prose but the artifact it names is absent from the
    repository, which would let the article cite evidence that no reader can
    open."""
    path = ROOT / "parts" / "lewm_instantiation.tex"
    if not path.exists():
        return []
    text = path.read_text(encoding="utf-8", errors="ignore")
    errors = []
    seen: set[str] = set()
    for match in re.finditer(r"\\path\{([^}]*)\}", text):
        target = match.group(1).strip()
        # Drop a trailing JSONPath selector such as ':$.not_claimed'.
        target = target.split(":$", 1)[0]
        if not (target.startswith("experiments/") or target.startswith("formal/")):
            continue
        if target in seen:
            continue
        seen.add(target)
        if not (ROOT / target).exists():
            errors.append(
                f"parts/lewm_instantiation.tex: evidence pointer does not resolve "
                f"to a repository artifact: {target}"
            )
    return errors


def run_check(name: str, errors: list[str], *, note: str | None = None) -> bool:
    if errors:
        print(f"[bedc-jepa precheck] {name}: FAIL", file=sys.stderr)
        for error in errors[:200]:
            print(f"- {error}", file=sys.stderr)
        if len(errors) > 200:
            print(f"- ... {len(errors) - 200} more", file=sys.stderr)
        return False
    suffix = f" ({note})" if note else ""
    print(f"[bedc-jepa precheck] {name}: PASS{suffix}")
    return True


def main() -> int:
    files = tex_files()
    checks = (
        ("check_tex_size", check_tex_size(files), None),
        ("check_math_env", check_math_env(files), None),
        ("check_text_macro_underscores", check_text_macro_underscores(files), None),
        ("check_up_macros", check_up_macros(files), None),
        ("check_external_provenance", check_external_provenance(files), None),
        ("check_no_iteration_narrative", check_no_iteration_narrative(files), None),
        ("check_gap_readback_claim_boundary", check_gap_readback_claim_boundary(files), None),
        ("check_gap_auc_claim_surfaces", check_gap_auc_claim_surfaces(files), None),
        ("check_no_undefined_refs_or_cites", check_references(files), None),
        ("check_environment_balance", check_env_balance(files), None),
        ("check_lewm_evidence_pointer", check_lewm_evidence_pointer(files), None),
        ("check_capability_promotion_contract", check_capability_promotion_contract(files), None),
        ("check_mechanism_target_claim_boundary", check_mechanism_target_claim_boundary(files), None),
        ("check_evidence_files_exist", check_evidence_files_exist(files), None),
        ("check_lean_markers", check_not_applicable_markers(files), "not applicable to this article, no markers present"),
        ("check_closurestatus", check_closurestatus(files), "not applicable to this article, no blocks present"),
    )
    ok = True
    for name, errors, note in checks:
        ok = run_check(name, errors, note=note) and ok
    if ok:
        print("[bedc-jepa precheck] all BEDC-style checks passed")
        return 0
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
