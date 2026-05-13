# Capstones-Intuition Pipeline 实施方案

> **给 agent worker:** 必需 sub-skill: 使用 superpowers:subagent-driven-development (推荐) 或 superpowers:executing-plans 来逐 task 实施. Steps 用 checkbox (`- [ ]`) 跟踪.

**目标:** 落地 `docs/superpowers/specs/2026-05-11-capstones-intuition-pipeline-spec.md` 描述的 gate-only harness. 在 `lean4/scripts/bedc_ci.py` 加 6 个 audit + 1 lint, 在 phase_review.txt / phase_revise.txt 加 prompt 约束. 不动 `papers/bedc/scripts/codex_revise.py` — 它的 phase VERIFY 已经在调 `bedc_ci.py audit`, 新 gate 自动生效. **不加 LaTeX 宏** — traceability 走 commit transparency block, 不污染 PDF 内容.

**架构:** TDD, `unittest.TestCase` 风格匹配 `lean4/scripts/test_closurestatus_audit.py`. Audit 是纯函数 `audit_<name>(repo_root, ...) -> list[str]`. 文件状态 audit 跑当前状态 + HEAD 增加文件. commit message audit 解析 HEAD commit body 内的 YAML transparency block. NN 冲突按 spec §5.4 容忍 (lint warn only).

**技术栈:** Python 3 stdlib only (regex / subprocess), 现有 `unittest` 测试基础设施.

---

## 文件结构

**新建文件 (1):**
- `lean4/scripts/test_capstones_pipeline_gates.py` — 新 audit 的全部单元测试

**修改文件 (3):**
- `lean4/scripts/bedc_ci.py` — 加 ~250 行: 6 个 audit + 1 lint + transparency YAML parser + STOP marker helper + wire 进 `audit` 子命令
- `papers/bedc/scripts/prompts/phase_review.txt` — 加 ~90 行: 2 个 HARD GATE 段 + transparency YAML schema 规范
- `papers/bedc/scripts/prompts/phase_revise.txt` — 加 ~25 行: commit message transparency block 模板

**不动文件:**
- `papers/bedc/scripts/codex_revise.py` — orchestrator 不变. phase VERIFY 已调 `bedc_ci.py audit`, 新 gate 自动 fire
- `papers/bedc/preamble.tex` — 不加 LaTeX 宏. Traceability 信息走 commit message 而非章节内容, 保持 PDF 干净

---

## Task 1: TDD G_derived_from_traceability audit (基于 commit transparency)

**文件:**
- 创建: `lean4/scripts/test_capstones_pipeline_gates.py`
- 修改: `lean4/scripts/bedc_ci.py`

- [ ] **Step 1: 写失败测试**

创建 `lean4/scripts/test_capstones_pipeline_gates.py`:

```python
"""Unit tests for the v5 capstones-intuition-pipeline gates in bedc_ci.py."""

from __future__ import annotations

import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from bedc_ci import (  # type: ignore[import-not-found]
    audit_derived_from_traceability,
)


class DerivedFromTraceabilityTests(unittest.TestCase):
    def setUp(self) -> None:
        self.repo = Path(tempfile.mkdtemp())
        (self.repo / "papers" / "bedc" / "parts" / "capstones").mkdir(parents=True)

    def _write_capstone(self, name: str) -> None:
        (self.repo / "papers" / "bedc" / "parts" / "capstones" / f"{name}.tex").write_text(
            rf"\chapter{{Test}}\label{{ch:visions-{name}}}"
        )

    def _msg_with_implemented(self, name: str, derivedfrom: str | None = None) -> str:
        df_line = f"\n    derivedfrom: {derivedfrom}" if derivedfrom else ""
        return textwrap.dedent(f"""
            P1000: add {name}

            ```transparency
            proposed_candidates: []
            rejected_candidates: []
            deferred_candidates: []
            implemented_targets:
              - name: {name}
                file: papers/bedc/parts/concrete_instances/99_x_namecert_construction.tex{df_line}
            ```
        """)

    def test_passes_when_no_derivedfrom(self) -> None:
        msg = self._msg_with_implemented("FooUp")
        self.assertEqual(audit_derived_from_traceability(msg, self.repo), [])

    def test_passes_when_derivedfrom_resolves(self) -> None:
        self._write_capstone("real-completeness")
        msg = self._msg_with_implemented("FooUp", "ch:visions-real-completeness")
        self.assertEqual(audit_derived_from_traceability(msg, self.repo), [])

    def test_fails_when_capstone_missing(self) -> None:
        msg = self._msg_with_implemented("FooUp", "ch:visions-nonexistent")
        issues = audit_derived_from_traceability(msg, self.repo)
        self.assertEqual(len(issues), 1)
        self.assertIn("nonexistent", issues[0])

    def test_fails_when_derivedfrom_malformed(self) -> None:
        msg = self._msg_with_implemented("FooUp", "not-a-capstone-label")
        issues = audit_derived_from_traceability(msg, self.repo)
        self.assertEqual(len(issues), 1)
        self.assertIn("malformed", issues[0])

    def test_passes_when_no_transparency_block(self) -> None:
        # No block means no audit possible; missing-block audit is separate.
        self.assertEqual(
            audit_derived_from_traceability("Plain commit.", self.repo), []
        )


if __name__ == "__main__":
    unittest.main()
```

- [ ] **Step 2: 跑测试, 应该 ImportError**

运行: `cd /Users/auric/newmath && python3 -m unittest lean4.scripts.test_capstones_pipeline_gates -v 2>&1 | tail -10`
预期: `ImportError: cannot import name 'audit_derived_from_traceability'`

- [ ] **Step 3: 添加 audit 函数到 bedc_ci.py**

`audit_derived_from_traceability` 依赖 `parse_transparency_block` (Task 3 实现). 先添加占位实现, Task 3 时填充:

在 `lean4/scripts/bedc_ci.py` 中合适位置 (类似 `audit_closurestatus_blocks` 附近) 添加:

```python
DERIVED_FROM_LABEL_RE = re.compile(r"^ch:visions-[a-z0-9-]+$")


def audit_derived_from_traceability(commit_message: str, repo_root: Path) -> list[str]:
    """G_derived_from_traceability: each implemented_target with a non-null
    `derivedfrom` field must reference a real capstone file.

    Reads from commit message transparency block (NOT inline LaTeX markers).
    Chapters without derivedfrom are valid (independent horizons).
    Returns issue list; empty = OK.
    """
    block = parse_transparency_block(commit_message)
    if block is None:
        return []
    issues: list[str] = []
    cap_root = repo_root / "papers" / "bedc" / "parts" / "capstones"
    for target in block.get("implemented_targets", []):
        if not isinstance(target, dict):
            continue
        derivedfrom = target.get("derivedfrom")
        if not derivedfrom:
            continue
        name = target.get("name", "<unnamed>")
        if not DERIVED_FROM_LABEL_RE.match(derivedfrom):
            issues.append(
                f"implemented_target '{name}': derivedfrom '{derivedfrom}' is malformed "
                f"(expected 'ch:visions-<theme>')"
            )
            continue
        theme = derivedfrom[len("ch:visions-"):]
        capstone_path = cap_root / f"{theme}.tex"
        if not capstone_path.exists():
            issues.append(
                f"implemented_target '{name}': derivedfrom references nonexistent "
                f"capstone '{derivedfrom}' (looked for {capstone_path})"
            )
    return issues
```

注意此时 `parse_transparency_block` 还不存在, Task 3 会加. 此 task 仅添加 `audit_derived_from_traceability` + 常量, 跑测试会因 `parse_transparency_block` 不存在而 fail. **Task 3 完成后 Task 1 的测试才能 PASS** — 这是合理的依赖, Task 1-3 是同一 audit 链路.

为让 TDD 节奏顺畅, 调整: Task 1 写测试 + audit 框架; Task 3 (parser) PASS 后, 跑回 Task 1 的测试确认通过.

- [ ] **Step 4: 提交 (测试此时未 pass)**

```bash
cd /Users/auric/newmath
git add lean4/scripts/test_capstones_pipeline_gates.py lean4/scripts/bedc_ci.py
git commit -m "Add G_derived_from_traceability skeleton (bedc_ci.py)

Function reads commit transparency block, validates each
implemented_target's derivedfrom field resolves to a real capstone.
Tests fail until parse_transparency_block lands (Task 3).

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

---

## Task 2: TDD STOP marker scan helper

**文件:**
- 修改: `lean4/scripts/test_capstones_pipeline_gates.py`
- 修改: `lean4/scripts/bedc_ci.py`

- [ ] **Step 1: 追加失败测试**

在 `lean4/scripts/test_capstones_pipeline_gates.py` 末尾 (`if __name__` 之前) 追加:

```python
class StopMarkerScanTests(unittest.TestCase):
    def setUp(self) -> None:
        self.path = Path(tempfile.mkdtemp()) / "capstone.tex"

    def test_finds_schema_only(self) -> None:
        self.path.write_text("L1\nnormal\nThis is SCHEMA-ONLY\nL4\n")
        from bedc_ci import scan_stop_markers_in_range
        hits = scan_stop_markers_in_range(self.path, 1, 4)
        self.assertTrue(any("SCHEMA-ONLY" in h for h in hits))

    def test_finds_deferred_to_future(self) -> None:
        self.path.write_text("Line1\ndeferred to future\nLine3\n")
        from bedc_ci import scan_stop_markers_in_range
        hits = scan_stop_markers_in_range(self.path, 1, 3)
        self.assertTrue(any("deferred to future" in h for h in hits))

    def test_empty_when_no_marker(self) -> None:
        self.path.write_text("Line1\nLine2\nLine3\n")
        from bedc_ci import scan_stop_markers_in_range
        self.assertEqual(scan_stop_markers_in_range(self.path, 1, 3), [])

    def test_respects_line_range(self) -> None:
        self.path.write_text("L1\nL2\nL3\nL4\nSCHEMA-ONLY\nL6\n")
        from bedc_ci import scan_stop_markers_in_range
        self.assertEqual(scan_stop_markers_in_range(self.path, 1, 3), [])
        self.assertTrue(scan_stop_markers_in_range(self.path, 1, 5))

    def test_missing_file_returns_empty(self) -> None:
        from bedc_ci import scan_stop_markers_in_range
        nonexistent = self.path.parent / "absent.tex"
        self.assertEqual(scan_stop_markers_in_range(nonexistent, 1, 10), [])
```

- [ ] **Step 2: 跑新测试, 应该 ImportError**

运行: `cd /Users/auric/newmath && python3 -m unittest lean4.scripts.test_capstones_pipeline_gates.StopMarkerScanTests -v 2>&1 | tail -10`
预期: `ImportError: cannot import name 'scan_stop_markers_in_range'`

- [ ] **Step 3: 添加 helper 到 bedc_ci.py**

在其他 helper 附近 (例如 `def read_text` 附近) 添加:

```python
STOP_MARKERS = (
    "SCHEMA-ONLY",
    "deferred to future",
    "not yet developed",
    "future development that does not yet exist",
)


def scan_stop_markers_in_range(path: Path, line_start: int, line_end: int) -> list[str]:
    """Return STOP markers found in path between line_start and line_end
    (inclusive, 1-based). Each return value is 'L<n>: <marker>'.

    Missing file / unreadable / out-of-range all return empty list.
    """
    if not path.exists():
        return []
    try:
        lines = path.read_text(encoding="utf-8", errors="ignore").splitlines()
    except OSError:
        return []
    hits: list[str] = []
    lo = max(1, line_start)
    hi = min(len(lines), line_end)
    for n in range(lo, hi + 1):
        line = lines[n - 1]
        for marker in STOP_MARKERS:
            if marker in line:
                hits.append(f"L{n}: {marker}")
                break
    return hits
```

- [ ] **Step 4: 跑测试, 应该 5 个新测试通过**

运行: `cd /Users/auric/newmath && python3 -m unittest lean4.scripts.test_capstones_pipeline_gates.StopMarkerScanTests -v 2>&1 | tail -10`
预期: 5 tests OK.

- [ ] **Step 5: 提交**

```bash
cd /Users/auric/newmath
git add lean4/scripts/test_capstones_pipeline_gates.py lean4/scripts/bedc_ci.py
git commit -m "Add scan_stop_markers_in_range helper (bedc_ci.py)

Detects 4 STOP marker strings (SCHEMA-ONLY, deferred to future,
not yet developed, future development that does not yet exist)
within a line range. Used by G_capstone_stop_respect.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

---

## Task 3: TDD transparency YAML parser

**文件:**
- 修改: `lean4/scripts/test_capstones_pipeline_gates.py`
- 修改: `lean4/scripts/bedc_ci.py`

- [ ] **Step 1: 追加失败测试**

```python
class TransparencyBlockParserTests(unittest.TestCase):
    def test_parse_well_formed_block(self) -> None:
        msg = textwrap.dedent("""
            P5556: add RegSeqRatUp naming certificate

            ```transparency
            proposed_candidates:
              - name: RegSeqRatUp
                source_capstone: real-completeness
                source_location: papers/bedc/parts/visions/real_completeness.tex:L40-L60
                taste_gate_feasibility:
                  bhist_carrier_sketch: "Bishop-style regular Cauchy stream"
                  conservativity_argument: "Adds carrier predicate over BHist"
                  no_hidden_input_argument: "Each token shown from b0,b1"
                  round_trip_argument: "Display reads dyadic radius"
                  layer_separation_argument: "Source/channel/display distinct"
            rejected_candidates: []
            deferred_candidates: []
            implemented_targets:
              - name: RegSeqRatUp
                file: papers/bedc/parts/concrete_instances/301_regseqrat_namecert_construction.tex
                derivedfrom: ch:visions-real-completeness
            ```
        """)
        from bedc_ci import parse_transparency_block
        result = parse_transparency_block(msg)
        self.assertIsNotNone(result)
        assert result is not None
        self.assertEqual(len(result["proposed_candidates"]), 1)
        self.assertEqual(result["proposed_candidates"][0]["name"], "RegSeqRatUp")
        feas = result["proposed_candidates"][0]["taste_gate_feasibility"]
        self.assertEqual(feas["bhist_carrier_sketch"], "Bishop-style regular Cauchy stream")
        self.assertEqual(result["implemented_targets"][0]["derivedfrom"],
                         "ch:visions-real-completeness")

    def test_returns_none_when_no_block(self) -> None:
        from bedc_ci import parse_transparency_block
        self.assertIsNone(parse_transparency_block("Plain commit."))

    def test_all_empty_lists(self) -> None:
        msg = textwrap.dedent("""
            ```transparency
            proposed_candidates: []
            rejected_candidates: []
            deferred_candidates: []
            implemented_targets: []
            ```
        """)
        from bedc_ci import parse_transparency_block
        result = parse_transparency_block(msg)
        self.assertIsNotNone(result)
        assert result is not None
        self.assertEqual(result["proposed_candidates"], [])
```

- [ ] **Step 2: 跑测试, 应该 ImportError**

运行: `cd /Users/auric/newmath && python3 -m unittest lean4.scripts.test_capstones_pipeline_gates.TransparencyBlockParserTests -v 2>&1 | tail -10`
预期: `ImportError: cannot import name 'parse_transparency_block'`

- [ ] **Step 3: 添加 hand-rolled YAML parser**

CLAUDE.md 要求 stdlib only. Python stdlib 无 YAML, 手写一个针对 spec §4.6 限定 schema 的 parser. 添加到 `bedc_ci.py`:

```python
TRANSPARENCY_BLOCK_RE = re.compile(r"```transparency\s*\n(.*?)\n```", re.DOTALL)


def parse_transparency_block(commit_message: str) -> dict | None:
    """Parse the ```transparency YAML block from a P-round commit message.

    Returns dict with 4 keys: proposed_candidates, rejected_candidates,
    deferred_candidates, implemented_targets. Each is list of dicts.
    Returns None if no block found.

    Focused hand-parser for the schema in spec §4.6 (list-of-dicts with
    single-level nesting). Not a general YAML parser.
    """
    m = TRANSPARENCY_BLOCK_RE.search(commit_message)
    if not m:
        return None
    return _parse_transparency_yaml_body(m.group(1))


def _parse_transparency_yaml_body(body: str) -> dict:
    result: dict[str, list] = {
        "proposed_candidates": [],
        "rejected_candidates": [],
        "deferred_candidates": [],
        "implemented_targets": [],
    }
    current_key: str | None = None
    current_entry: dict | None = None
    current_nested_key: str | None = None
    for raw in body.splitlines():
        line = raw.rstrip()
        if not line.strip():
            continue
        m_empty = re.match(r"^([a-z_]+):\s*\[\s*\]\s*$", line)
        if m_empty:
            current_key = m_empty.group(1)
            if current_key in result:
                result[current_key] = []
            current_entry = None
            current_nested_key = None
            continue
        m_top = re.match(r"^([a-z_]+):\s*$", line)
        if m_top:
            current_key = m_top.group(1) if m_top.group(1) in result else None
            current_entry = None
            current_nested_key = None
            continue
        m_entry = re.match(r"^\s+-\s+([a-z_]+):\s*(.*)$", line)
        if m_entry and current_key:
            current_entry = {}
            result[current_key].append(current_entry)
            key, value = m_entry.group(1), m_entry.group(2)
            current_entry[key] = _strip_yaml_value(value)
            current_nested_key = None
            continue
        m_cont = re.match(r"^\s{4,}([a-z_]+):\s*(.*)$", line)
        if m_cont and current_entry is not None:
            key, value = m_cont.group(1), m_cont.group(2)
            if not value.strip():
                current_nested_key = key
                current_entry[key] = {}
            else:
                target = (
                    current_entry[current_nested_key]
                    if current_nested_key
                    and isinstance(current_entry.get(current_nested_key), dict)
                    else current_entry
                )
                target[key] = _strip_yaml_value(value)
            continue
    return result


def _strip_yaml_value(raw: str) -> str:
    v = raw.strip()
    if (v.startswith('"') and v.endswith('"')) or (v.startswith("'") and v.endswith("'")):
        v = v[1:-1]
    return v
```

- [ ] **Step 4: 跑测试, 此时 Task 1 + Task 3 测试都应通过**

运行: `cd /Users/auric/newmath && python3 -m unittest lean4.scripts.test_capstones_pipeline_gates -v 2>&1 | tail -20`
预期: 13 tests pass (5 derivedfrom + 5 stop + 3 parser).

- [ ] **Step 5: 提交**

```bash
cd /Users/auric/newmath
git add lean4/scripts/test_capstones_pipeline_gates.py lean4/scripts/bedc_ci.py
git commit -m "Add parse_transparency_block hand-rolled YAML parser (bedc_ci.py)

Parses the restricted YAML schema in spec §4.6 (4 top-level keys,
list-of-dicts entries, single-level nesting) from P-round commit
message fenced \`\`\`transparency block. Stdlib-only per CLAUDE.md.

Unblocks G_derived_from_traceability tests (now pass) and is consumed
by G_capstone_stop_respect + G_taste_gate_feasibility.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

---

## Task 4: TDD G_capstone_stop_respect audit

**文件:**
- 修改: `lean4/scripts/test_capstones_pipeline_gates.py`
- 修改: `lean4/scripts/bedc_ci.py`

- [ ] **Step 1: 追加失败测试**

```python
class CapstoneStopRespectAuditTests(unittest.TestCase):
    def setUp(self) -> None:
        self.repo = Path(tempfile.mkdtemp())
        cap_dir = self.repo / "papers" / "bedc" / "parts" / "capstones"
        cap_dir.mkdir(parents=True)
        (cap_dir / "inter-hist-locality.tex").write_text(textwrap.dedent("""
            \\chapter{Inter-Hist Locality}
            Normal narrative on line 2.
            Multi-Hist configurations paragraph.
            More normal narrative.
            This section is SCHEMA-ONLY for the future.
            Causal rate is observer-symmetric here.
        """).lstrip())

    def _msg(self, name: str, line_range: str, deferred: bool = False) -> str:
        if deferred:
            section_body = textwrap.dedent(f"""\
            deferred_candidates:
              - concept: {name}
                source_capstone: inter-hist-locality
                source_location: papers/bedc/parts/visions/inter-hist-locality.tex:{line_range}
                stop_marker_text: "SCHEMA-ONLY"
            proposed_candidates: []""")
        else:
            section_body = textwrap.dedent(f"""\
            proposed_candidates:
              - name: {name}
                source_capstone: inter-hist-locality
                source_location: papers/bedc/parts/visions/inter-hist-locality.tex:{line_range}
                taste_gate_feasibility:
                  bhist_carrier_sketch: "ok"
                  conservativity_argument: "ok"
                  no_hidden_input_argument: "ok"
                  round_trip_argument: "ok"
                  layer_separation_argument: "ok"
            deferred_candidates: []""")
        return textwrap.dedent(f"""
            P1000: test

            ```transparency
            {section_body}
            rejected_candidates: []
            implemented_targets: []
            ```
        """)

    def test_passes_when_no_candidate_in_stop_region(self) -> None:
        from bedc_ci import audit_capstone_stop_respect
        msg = self._msg("MultiHistConfigUp", "L1-L4")
        self.assertEqual(audit_capstone_stop_respect(msg, self.repo), [])

    def test_fails_when_candidate_in_stop_region(self) -> None:
        from bedc_ci import audit_capstone_stop_respect
        msg = self._msg("CausalRateUp", "L5-L6")
        issues = audit_capstone_stop_respect(msg, self.repo)
        self.assertEqual(len(issues), 1)
        self.assertIn("SCHEMA-ONLY", issues[0])
        self.assertIn("CausalRateUp", issues[0])

    def test_passes_when_stop_region_candidate_is_deferred(self) -> None:
        from bedc_ci import audit_capstone_stop_respect
        msg = self._msg("CausalRateUp", "L5-L6", deferred=True)
        self.assertEqual(audit_capstone_stop_respect(msg, self.repo), [])

    def test_handles_missing_transparency_block(self) -> None:
        from bedc_ci import audit_capstone_stop_respect
        self.assertEqual(audit_capstone_stop_respect("Plain commit.", self.repo), [])
```

- [ ] **Step 2: 跑测试, 应该 ImportError**

运行: `cd /Users/auric/newmath && python3 -m unittest lean4.scripts.test_capstones_pipeline_gates.CapstoneStopRespectAuditTests -v 2>&1 | tail -10`
预期: `ImportError: cannot import name 'audit_capstone_stop_respect'`

- [ ] **Step 3: 添加 audit**

在 `bedc_ci.py` 添加:

```python
SOURCE_LOCATION_RE = re.compile(r"^(.+?):L(\d+)-L(\d+)$")


def audit_capstone_stop_respect(commit_message: str, repo_root: Path) -> list[str]:
    """G_capstone_stop_respect: 每个 proposed_candidate, 扫其 source_location
    line range 找 STOP markers. 若发现 STOP 且 candidate 不在 deferred_candidates,
    audit fail.

    Returns issue list; empty = OK. 无 transparency block = [] (其他 audit 管缺失).
    """
    block = parse_transparency_block(commit_message)
    if block is None:
        return []
    issues: list[str] = []
    deferred_names = {
        e.get("concept") for e in block.get("deferred_candidates", [])
        if isinstance(e, dict)
    }
    for entry in block.get("proposed_candidates", []):
        if not isinstance(entry, dict):
            continue
        name = entry.get("name", "<unnamed>")
        if name in deferred_names:
            continue
        loc = entry.get("source_location", "")
        m = SOURCE_LOCATION_RE.match(loc)
        if not m:
            continue
        rel_path, lo, hi = m.group(1), int(m.group(2)), int(m.group(3))
        path = repo_root / rel_path
        hits = scan_stop_markers_in_range(path, lo, hi)
        if hits:
            issues.append(
                f"candidate '{name}' proposed despite STOP markers in "
                f"{rel_path}:L{lo}-L{hi} ({'; '.join(hits)})"
            )
    return issues
```

- [ ] **Step 4: 跑测试**

运行: `cd /Users/auric/newmath && python3 -m unittest lean4.scripts.test_capstones_pipeline_gates -v 2>&1 | tail -20`
预期: 17 tests pass.

- [ ] **Step 5: 提交**

```bash
cd /Users/auric/newmath
git add lean4/scripts/test_capstones_pipeline_gates.py lean4/scripts/bedc_ci.py
git commit -m "Add audit_capstone_stop_respect (G_capstone_stop_respect)

每个 P-round proposed candidate, 读 source_location 范围, 扫 STOP
markers. STOP 命中且 candidate 不在 deferred_candidates 则 audit fail.
实施 spec §4.3 / D2 hard gate.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

---

## Task 5: TDD G_taste_gate_feasibility audit

**文件:**
- 修改: `lean4/scripts/test_capstones_pipeline_gates.py`
- 修改: `lean4/scripts/bedc_ci.py`

- [ ] **Step 1: 追加失败测试**

```python
class TasteGateFeasibilityAuditTests(unittest.TestCase):
    def _msg_with_feasibility(self, **overrides) -> str:
        defaults = {
            "bhist_carrier_sketch": "carrier ok",
            "conservativity_argument": "conservativity ok",
            "no_hidden_input_argument": "no hidden input ok",
            "round_trip_argument": "round trip ok",
            "layer_separation_argument": "layer separation ok",
        }
        defaults.update(overrides)
        feas_lines = "\n".join(f'      {k}: "{v}"' for k, v in defaults.items())
        return textwrap.dedent(f"""
            P1100: add FooUp

            ```transparency
            proposed_candidates:
              - name: FooUp
                source_capstone: null
                source_location: x.tex:L1-L1
                taste_gate_feasibility:
{feas_lines}
            rejected_candidates: []
            deferred_candidates: []
            implemented_targets: []
            ```
        """)

    def test_passes_when_all_5_fields_nonempty(self) -> None:
        from bedc_ci import audit_taste_gate_feasibility
        self.assertEqual(audit_taste_gate_feasibility(self._msg_with_feasibility()), [])

    def test_fails_when_bhist_carrier_empty(self) -> None:
        from bedc_ci import audit_taste_gate_feasibility
        issues = audit_taste_gate_feasibility(
            self._msg_with_feasibility(bhist_carrier_sketch="")
        )
        self.assertEqual(len(issues), 1)
        self.assertIn("bhist_carrier_sketch", issues[0])
        self.assertIn("empty", issues[0])

    def test_fails_when_field_is_fails(self) -> None:
        from bedc_ci import audit_taste_gate_feasibility
        issues = audit_taste_gate_feasibility(
            self._msg_with_feasibility(no_hidden_input_argument="fails")
        )
        self.assertEqual(len(issues), 1)
        self.assertIn("no_hidden_input_argument", issues[0])
        self.assertIn("fails", issues[0])

    def test_fails_when_field_missing(self) -> None:
        from bedc_ci import audit_taste_gate_feasibility
        msg = textwrap.dedent("""
            P1101: add FooUp

            ```transparency
            proposed_candidates:
              - name: FooUp
                source_capstone: null
                source_location: x.tex:L1-L1
                taste_gate_feasibility:
                  bhist_carrier_sketch: "ok"
                  conservativity_argument: "ok"
                  no_hidden_input_argument: "ok"
                  round_trip_argument: "ok"
            rejected_candidates: []
            deferred_candidates: []
            implemented_targets: []
            ```
        """)
        issues = audit_taste_gate_feasibility(msg)
        self.assertEqual(len(issues), 1)
        self.assertIn("layer_separation_argument", issues[0])
        self.assertIn("missing", issues[0])

    def test_passes_when_no_proposed_candidates(self) -> None:
        from bedc_ci import audit_taste_gate_feasibility
        msg = textwrap.dedent("""
            ```transparency
            proposed_candidates: []
            rejected_candidates: []
            deferred_candidates: []
            implemented_targets: []
            ```
        """)
        self.assertEqual(audit_taste_gate_feasibility(msg), [])
```

- [ ] **Step 2: 跑测试**

运行: `cd /Users/auric/newmath && python3 -m unittest lean4.scripts.test_capstones_pipeline_gates.TasteGateFeasibilityAuditTests -v 2>&1 | tail -10`
预期: `ImportError: cannot import name 'audit_taste_gate_feasibility'`

- [ ] **Step 3: 添加 audit**

```python
REQUIRED_FEASIBILITY_FIELDS = (
    "bhist_carrier_sketch",
    "conservativity_argument",
    "no_hidden_input_argument",
    "round_trip_argument",
    "layer_separation_argument",
)


def audit_taste_gate_feasibility(commit_message: str) -> list[str]:
    """G_taste_gate_feasibility: 每个 proposed_candidate 必须含
    taste_gate_feasibility dict, 内含 5 个 required 字段, 各非空且不等于 'fails'.
    """
    block = parse_transparency_block(commit_message)
    if block is None:
        return []
    issues: list[str] = []
    for entry in block.get("proposed_candidates", []):
        if not isinstance(entry, dict):
            continue
        name = entry.get("name", "<unnamed>")
        feas = entry.get("taste_gate_feasibility")
        if not isinstance(feas, dict):
            issues.append(f"candidate '{name}': taste_gate_feasibility missing or malformed")
            continue
        for field in REQUIRED_FEASIBILITY_FIELDS:
            value = feas.get(field)
            if value is None:
                issues.append(f"candidate '{name}': {field} missing")
            elif not str(value).strip():
                issues.append(f"candidate '{name}': {field} empty")
            elif str(value).strip().lower() == "fails":
                issues.append(f"candidate '{name}': {field} == 'fails' (admission gate failed)")
    return issues
```

- [ ] **Step 4: 跑测试**

运行: `cd /Users/auric/newmath && python3 -m unittest lean4.scripts.test_capstones_pipeline_gates -v 2>&1 | tail -25`
预期: 22 tests pass.

- [ ] **Step 5: 提交**

```bash
cd /Users/auric/newmath
git add lean4/scripts/test_capstones_pipeline_gates.py lean4/scripts/bedc_ci.py
git commit -m "Add audit_taste_gate_feasibility (G_taste_gate_feasibility)

每个 proposed_candidate 必须有完整 5 字段 taste_gate_feasibility, 各
非空且不等于 'fails'. 实施 spec §4.2 / D1.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

---

## Task 6: TDD G_emergency_brake audit

**文件:**
- 修改: `lean4/scripts/test_capstones_pipeline_gates.py`
- 修改: `lean4/scripts/bedc_ci.py`

- [ ] **Step 1: 追加失败测试**

```python
class EmergencyBrakeAuditTests(unittest.TestCase):
    def setUp(self) -> None:
        self.repo = Path(tempfile.mkdtemp())
        (self.repo / "papers" / "bedc").mkdir(parents=True)

    def test_passes_when_brake_file_absent(self) -> None:
        from bedc_ci import audit_emergency_brake
        self.assertEqual(audit_emergency_brake(self.repo, head_added_files=[]), [])

    def test_passes_when_brake_active_but_no_new_chapter(self) -> None:
        from bedc_ci import audit_emergency_brake
        (self.repo / "papers" / "bedc" / ".creation_paused").touch()
        self.assertEqual(
            audit_emergency_brake(
                self.repo,
                head_added_files=["papers/bedc/parts/concrete_instances/field/sub.tex"],
            ),
            [],
        )

    def test_fails_when_brake_active_and_new_top_chapter(self) -> None:
        from bedc_ci import audit_emergency_brake
        (self.repo / "papers" / "bedc" / ".creation_paused").touch()
        issues = audit_emergency_brake(
            self.repo,
            head_added_files=[
                "papers/bedc/parts/concrete_instances/999_foo_namecert_construction.tex"
            ],
        )
        self.assertEqual(len(issues), 1)
        self.assertIn("creation_paused", issues[0])
        self.assertIn("999_foo", issues[0])
```

- [ ] **Step 2: 跑测试**

运行: `cd /Users/auric/newmath && python3 -m unittest lean4.scripts.test_capstones_pipeline_gates.EmergencyBrakeAuditTests -v 2>&1 | tail -10`
预期: `ImportError`

- [ ] **Step 3: 添加 audit**

```python
NEW_TOP_CHAPTER_RE = re.compile(
    r"^papers/bedc/parts/concrete_instances/\d+_[a-z][a-z0-9_]*_namecert_construction\.tex$"
)


def audit_emergency_brake(repo_root: Path, head_added_files: list[str]) -> list[str]:
    """G_emergency_brake: 若 papers/bedc/.creation_paused 存在且 HEAD 加新
    顶层 concrete_instances chapter, audit fail.

    head_added_files = HEAD commit 加入的相对路径列表. Sibling 文件 (在
    subdir 下) 不算新顶层 chapter, 通过.
    """
    brake_path = repo_root / "papers" / "bedc" / ".creation_paused"
    if not brake_path.exists():
        return []
    issues: list[str] = []
    for path in head_added_files:
        if NEW_TOP_CHAPTER_RE.match(path):
            issues.append(
                f"emergency brake active (papers/bedc/.creation_paused exists); "
                f"new top-level chapter '{path}' rejected. Remove brake file to resume."
            )
    return issues
```

- [ ] **Step 4: 跑测试**

运行: `cd /Users/auric/newmath && python3 -m unittest lean4.scripts.test_capstones_pipeline_gates -v 2>&1 | tail -30`
预期: 25 tests pass.

- [ ] **Step 5: 提交**

```bash
cd /Users/auric/newmath
git add lean4/scripts/test_capstones_pipeline_gates.py lean4/scripts/bedc_ci.py
git commit -m "Add audit_emergency_brake (G_emergency_brake)

存在 papers/bedc/.creation_paused 时, 拒绝任何 HEAD 添加的新顶层
concrete_instances chapter. Sibling 文件不受影响. User 单行控制:
touch / rm 该文件.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

---

## Task 7: TDD G_daily_rate audit

**文件:**
- 修改: `lean4/scripts/test_capstones_pipeline_gates.py`
- 修改: `lean4/scripts/bedc_ci.py`

- [ ] **Step 1: 追加失败测试**

```python
class DailyRateAuditTests(unittest.TestCase):
    def test_passes_below_cap(self) -> None:
        from bedc_ci import check_daily_rate
        self.assertEqual(check_daily_rate(recent_24h_count=5, cap=10), [])

    def test_passes_at_cap_exactly(self) -> None:
        from bedc_ci import check_daily_rate
        self.assertEqual(check_daily_rate(recent_24h_count=10, cap=10), [])

    def test_fails_when_over_cap(self) -> None:
        from bedc_ci import check_daily_rate
        issues = check_daily_rate(recent_24h_count=11, cap=10)
        self.assertEqual(len(issues), 1)
        self.assertIn("daily rate", issues[0].lower())
        self.assertIn("11", issues[0])

    def test_count_helper_returns_zero_in_non_git_repo(self) -> None:
        from bedc_ci import count_new_top_chapters_in_last_24h
        self.assertEqual(count_new_top_chapters_in_last_24h(Path(tempfile.mkdtemp())), 0)
```

- [ ] **Step 2: 跑测试**

运行: `cd /Users/auric/newmath && python3 -m unittest lean4.scripts.test_capstones_pipeline_gates.DailyRateAuditTests -v 2>&1 | tail -10`
预期: `ImportError`

- [ ] **Step 3: 添加 audit**

```python
DAILY_NEW_CHAPTER_CAP_DEFAULT = 10


def count_new_top_chapters_in_last_24h(repo_root: Path) -> int:
    """统计过去 24h 新加的顶层 concrete_instances chapter 数. 非 git repo
    或 git 不可用返回 0.
    """
    import subprocess
    try:
        out = subprocess.check_output(
            [
                "git", "-C", str(repo_root), "log",
                "--since=24 hours ago", "--diff-filter=A",
                "--name-only", "--pretty=format:",
            ],
            text=True,
            stderr=subprocess.DEVNULL,
        )
    except (subprocess.CalledProcessError, FileNotFoundError):
        return 0
    return sum(
        1
        for line in out.splitlines()
        if line.strip() and NEW_TOP_CHAPTER_RE.match(line.strip())
    )


def check_daily_rate(
    recent_24h_count: int, cap: int = DAILY_NEW_CHAPTER_CAP_DEFAULT
) -> list[str]:
    """G_daily_rate: 24h 滚动窗口超过 cap 则报错. 纯函数, 调用方传入
    count (通常来自 count_new_top_chapters_in_last_24h).
    """
    if recent_24h_count > cap:
        return [
            f"daily rate limit exceeded: {recent_24h_count} new top-level "
            f"chapters in last 24h (cap {cap}). Override via .pipeline_parallel.json "
            f"key 'daily_new_chapter_cap'."
        ]
    return []
```

- [ ] **Step 4: 跑测试**

运行: `cd /Users/auric/newmath && python3 -m unittest lean4.scripts.test_capstones_pipeline_gates -v 2>&1 | tail -30`
预期: 29 tests pass.

- [ ] **Step 5: 提交**

```bash
cd /Users/auric/newmath
git add lean4/scripts/test_capstones_pipeline_gates.py lean4/scripts/bedc_ci.py
git commit -m "Add G_daily_rate audit (check_daily_rate + count helper)

24h 内新顶层 chapter 数 cap 10. 计数走 git log --since=24h --diff-filter=A.
通过 .pipeline_parallel.json key 'daily_new_chapter_cap' 覆盖.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

---

## Task 8: TDD G_theme_saturation_enhanced audit

**文件:**
- 修改: `lean4/scripts/test_capstones_pipeline_gates.py`
- 修改: `lean4/scripts/bedc_ci.py`

- [ ] **Step 1: 追加失败测试**

```python
class ThemeSaturationAuditTests(unittest.TestCase):
    def setUp(self) -> None:
        self.repo = Path(tempfile.mkdtemp())
        self.ci = self.repo / "papers" / "bedc" / "parts" / "concrete_instances"
        self.ci.mkdir(parents=True)

    def test_passes_for_new_theme(self) -> None:
        from bedc_ci import audit_theme_saturation
        self.assertEqual(
            audit_theme_saturation(
                self.repo,
                head_added_files=[
                    "papers/bedc/parts/concrete_instances/200_newtheme_namecert_construction.tex"
                ],
            ),
            [],
        )

    def test_passes_below_cap(self) -> None:
        from bedc_ci import audit_theme_saturation
        (self.ci / "field").mkdir()
        for i in range(10):
            (self.ci / "field" / f"20_field_sub{i}.tex").write_text("")
        self.assertEqual(
            audit_theme_saturation(
                self.repo,
                head_added_files=[
                    "papers/bedc/parts/concrete_instances/200_field_ext_namecert_construction.tex"
                ],
                cap=80,
            ),
            [],
        )

    def test_fails_at_cap(self) -> None:
        from bedc_ci import audit_theme_saturation
        (self.ci / "field").mkdir()
        for i in range(80):
            (self.ci / "field" / f"20_field_sub{i}.tex").write_text("")
        issues = audit_theme_saturation(
            self.repo,
            head_added_files=[
                "papers/bedc/parts/concrete_instances/200_field_ext_namecert_construction.tex"
            ],
            cap=80,
        )
        self.assertEqual(len(issues), 1)
        self.assertIn("field", issues[0])

    def test_sibling_extension_allowed_even_saturated(self) -> None:
        from bedc_ci import audit_theme_saturation
        (self.ci / "field").mkdir()
        for i in range(80):
            (self.ci / "field" / f"20_field_sub{i}.tex").write_text("")
        self.assertEqual(
            audit_theme_saturation(
                self.repo,
                head_added_files=["papers/bedc/parts/concrete_instances/field/new_lemma.tex"],
                cap=80,
            ),
            [],
        )
```

- [ ] **Step 2: 跑测试**

运行: `cd /Users/auric/newmath && python3 -m unittest lean4.scripts.test_capstones_pipeline_gates.ThemeSaturationAuditTests -v 2>&1 | tail -10`
预期: `ImportError`

- [ ] **Step 3: 添加 audit**

```python
THEME_SATURATION_CAP_DEFAULT = 80


def _extract_theme_from_chapter_path(path: str) -> str | None:
    """从 papers/bedc/parts/concrete_instances/<NN>_<slug>_namecert_construction.tex
    提取 theme = <slug> 的首段. 不匹配该 pattern 返回 None.
    """
    m = re.match(
        r"^papers/bedc/parts/concrete_instances/\d+_([a-z][a-z0-9]*)"
        r"(?:_[a-z0-9_]+)?_namecert_construction\.tex$",
        path,
    )
    return m.group(1) if m else None


def audit_theme_saturation(
    repo_root: Path,
    head_added_files: list[str],
    cap: int = THEME_SATURATION_CAP_DEFAULT,
) -> list[str]:
    """G_theme_saturation_enhanced: HEAD 新顶层 chapter 的 theme 已有 cap+
    文件 (top + subdir 合计) 则拒. Sibling 文件不算新顶层, 自动通过.
    """
    ci_root = repo_root / "papers" / "bedc" / "parts" / "concrete_instances"
    issues: list[str] = []
    for path in head_added_files:
        theme = _extract_theme_from_chapter_path(path)
        if theme is None:
            continue
        count = 0
        subdir = ci_root / theme
        if subdir.exists():
            count += sum(1 for _ in subdir.rglob("*.tex"))
        if ci_root.exists():
            for p in ci_root.iterdir():
                if p.is_file() and p.suffix == ".tex":
                    if re.match(rf"^\d+_{theme}(?:_|_namecert)", p.name):
                        count += 1
        if count >= cap:
            issues.append(
                f"theme '{theme}' saturated: {count} files (top + subdir) >= cap {cap}. "
                f"New top-level chapter '{path}' rejected. Extend existing chapters instead."
            )
    return issues
```

- [ ] **Step 4: 跑测试**

运行: `cd /Users/auric/newmath && python3 -m unittest lean4.scripts.test_capstones_pipeline_gates -v 2>&1 | tail -30`
预期: 33 tests pass.

- [ ] **Step 5: 提交**

```bash
cd /Users/auric/newmath
git add lean4/scripts/test_capstones_pipeline_gates.py lean4/scripts/bedc_ci.py
git commit -m "Add audit_theme_saturation (G_theme_saturation_enhanced)

Theme (top + subdir 文件合计) 已 80+ 则拒新顶层 chapter. Sibling 文件
不受影响. 防止 'field/' 类 137 文件深化继续产生新顶层主题.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

---

## Task 9: TDD NN duplicate lint (warn-only)

**文件:**
- 修改: `lean4/scripts/test_capstones_pipeline_gates.py`
- 修改: `lean4/scripts/bedc_ci.py`

- [ ] **Step 1: 追加失败测试**

```python
class NnDuplicateLintTests(unittest.TestCase):
    def setUp(self) -> None:
        self.repo = Path(tempfile.mkdtemp())
        self.ci = self.repo / "papers" / "bedc" / "parts" / "concrete_instances"
        self.ci.mkdir(parents=True)

    def test_no_warn_when_unique(self) -> None:
        from bedc_ci import lint_nn_duplicates
        (self.ci / "04_nat_namecert_construction.tex").write_text("")
        (self.ci / "05_add_namecert_construction.tex").write_text("")
        self.assertEqual(lint_nn_duplicates(self.repo), [])

    def test_warns_when_duplicate(self) -> None:
        from bedc_ci import lint_nn_duplicates
        (self.ci / "271_cauchymodulus_namecert_construction.tex").write_text("")
        (self.ci / "271_controlobservability_namecert_construction.tex").write_text("")
        (self.ci / "271_dyadicratcore_namecert_construction.tex").write_text("")
        warns = lint_nn_duplicates(self.repo)
        self.assertEqual(len(warns), 1)
        self.assertIn("271", warns[0])
        self.assertIn("3", warns[0])

    def test_multiple_groups(self) -> None:
        from bedc_ci import lint_nn_duplicates
        (self.ci / "271_a_namecert_construction.tex").write_text("")
        (self.ci / "271_b_namecert_construction.tex").write_text("")
        (self.ci / "272_a_namecert_construction.tex").write_text("")
        (self.ci / "272_b_namecert_construction.tex").write_text("")
        warns = lint_nn_duplicates(self.repo)
        self.assertEqual(len(warns), 2)
```

- [ ] **Step 2: 跑测试**

运行: `cd /Users/auric/newmath && python3 -m unittest lean4.scripts.test_capstones_pipeline_gates.NnDuplicateLintTests -v 2>&1 | tail -10`
预期: `ImportError`

- [ ] **Step 3: 添加 lint**

```python
def lint_nn_duplicates(repo_root: Path) -> list[str]:
    """NN 重复 lint warn (per spec §5.4): 不 fail, 只汇报已经发生的
    race (271×3 / 272×2 / 273×4 / 等). 未来 race 同样可见.
    """
    ci_root = repo_root / "papers" / "bedc" / "parts" / "concrete_instances"
    if not ci_root.exists():
        return []
    nn_map: dict[str, list[str]] = {}
    for p in ci_root.iterdir():
        if not (p.is_file() and p.suffix == ".tex"):
            continue
        m = re.match(r"^(\d+)_", p.name)
        if m:
            nn_map.setdefault(m.group(1), []).append(p.name)
    warns: list[str] = []
    for nn, names in sorted(nn_map.items()):
        if len(names) > 1:
            warns.append(
                f"NN {nn} used by {len(names)} chapters: {', '.join(sorted(names))}"
            )
    return warns
```

- [ ] **Step 4: 跑测试**

运行: `cd /Users/auric/newmath && python3 -m unittest lean4.scripts.test_capstones_pipeline_gates -v 2>&1 | tail -30`
预期: 36 tests pass.

- [ ] **Step 5: 提交**

```bash
cd /Users/auric/newmath
git add lean4/scripts/test_capstones_pipeline_gates.py lean4/scripts/bedc_ci.py
git commit -m "Add lint_nn_duplicates (warn-only)

汇报 NN 冲突 (271×3 / 272×2 / 273×4 已存在). 按 spec §5.4 容忍,
audit 看见 warn 但不 fail.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

---

## Task 10: 把所有新 audit wire 到 bedc_ci.py audit 子命令

**文件:**
- 修改: `lean4/scripts/bedc_ci.py`

- [ ] **Step 1: 找 audit 子命令 dispatcher**

运行: `cd /Users/auric/newmath && grep -nE "def cmd_audit|add_parser\\(.audit.\\)" lean4/scripts/bedc_ci.py | head`
预期: dispatch 位置的行号.

- [ ] **Step 2: 添加 HEAD commit 信息 helper**

在其他 helper 附近添加:

```python
def _current_commit_message(repo_root: Path) -> str:
    """Return HEAD commit message body, 或 '' 若非 git repo."""
    import subprocess
    try:
        return subprocess.check_output(
            ["git", "-C", str(repo_root), "log", "-1", "--pretty=%B"],
            text=True,
            stderr=subprocess.DEVNULL,
        )
    except (subprocess.CalledProcessError, FileNotFoundError):
        return ""


def _head_added_files(repo_root: Path) -> list[str]:
    """HEAD commit 加入 (A) 的相对路径列表."""
    import subprocess
    try:
        out = subprocess.check_output(
            [
                "git", "-C", str(repo_root), "show",
                "--diff-filter=A", "--name-only", "--pretty=format:", "HEAD",
            ],
            text=True,
            stderr=subprocess.DEVNULL,
        )
    except (subprocess.CalledProcessError, FileNotFoundError):
        return []
    return [line.strip() for line in out.splitlines() if line.strip()]


def _is_p_round_commit(message: str) -> bool:
    return bool(re.match(r"^P\d+:\s", message))
```

- [ ] **Step 3: 把新 audit wire 进 audit dispatcher**

在 `cmd_audit` (或等价函数) 既有 audit 调用之后, 追加:

```python
    # v5 capstones-intuition-pipeline gates
    repo = REPO_ROOT  # adjust to existing variable name

    head_msg = _current_commit_message(repo)
    head_added = _head_added_files(repo)
    head_adds_top_chapter = any(NEW_TOP_CHAPTER_RE.match(f) for f in head_added)

    # commit-message-driven gates: 仅当 HEAD 是 P-round 时跑
    if _is_p_round_commit(head_msg):
        for issue in audit_derived_from_traceability(head_msg, repo):
            print(f"[G_derived_from_traceability] {issue}", file=sys.stderr)
            exit_code = 1
        for issue in audit_capstone_stop_respect(head_msg, repo):
            print(f"[G_capstone_stop_respect] {issue}", file=sys.stderr)
            exit_code = 1
        for issue in audit_taste_gate_feasibility(head_msg):
            print(f"[G_taste_gate_feasibility] {issue}", file=sys.stderr)
            exit_code = 1

    # filesystem-state gates: 仅当 HEAD 加新顶层 chapter 时 fire
    # 原因: 这些 gate 关于"新 chapter 创建", 不是回溯状态
    if head_adds_top_chapter:
        for issue in audit_emergency_brake(repo, head_added):
            print(f"[G_emergency_brake] {issue}", file=sys.stderr)
            exit_code = 1

        recent_count = count_new_top_chapters_in_last_24h(repo)
        for issue in check_daily_rate(recent_count):
            print(f"[G_daily_rate] {issue}", file=sys.stderr)
            exit_code = 1

        for issue in audit_theme_saturation(repo, head_added):
            print(f"[G_theme_saturation_enhanced] {issue}", file=sys.stderr)
            exit_code = 1

    # warn-only lint: 总是跑
    for warn in lint_nn_duplicates(repo):
        print(f"[nn_duplicate_lint] WARN: {warn}", file=sys.stderr)
```

- [ ] **Step 4: 当前 repo smoke test**

运行: `cd /Users/auric/newmath && python3 lean4/scripts/bedc_ci.py audit 2>&1 | tail -25`
预期: exit 0. 输出可能含 `[nn_duplicate_lint] WARN: NN 271 used by 3 chapters: ...` 等 warn (现有 race), 但不影响 exit code. HEAD 是这次 wire 提交而非 P-round, 故 commit-message gate 跳过. HEAD 不加新顶层 chapter, 故 filesystem-state gate 也跳过.

- [ ] **Step 5: 验证所有现有测试仍通过**

运行: `cd /Users/auric/newmath && python3 -m unittest lean4.scripts.test_closurestatus_audit lean4.scripts.test_capstones_pipeline_gates 2>&1 | tail -5`
预期: 全部 OK (现有测试 + 36 新测试).

- [ ] **Step 6: 提交**

```bash
cd /Users/auric/newmath
git add lean4/scripts/bedc_ci.py
git commit -m "Wire v5 capstones-pipeline gates into bedc_ci.py audit subcommand

audit 现在还跑:
- 3 commit-message gates (仅 P-round): G_derived_from_traceability,
  G_capstone_stop_respect, G_taste_gate_feasibility
- 3 filesystem-state gates (仅当 HEAD 加新顶层 chapter):
  G_emergency_brake, G_daily_rate, G_theme_saturation_enhanced
- 1 warn-only lint: lint_nn_duplicates

codex_revise.py 的 phase VERIFY 已调 bedc_ci.py audit, 新 gate 自动 fire.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

---

## Task 11: phase_review.txt — G_taste_gate_feasibility HARD GATE

**文件:**
- 修改: `papers/bedc/scripts/prompts/phase_review.txt`

- [ ] **Step 1: bump prompt version**

运行: `cd /Users/auric/newmath && grep -n "## Prompts version" papers/bedc/scripts/prompts/phase_review.txt`
预期: 一行 + 紧随版本号 (e.g. `v5.16`). bump 到下一版 (e.g. `v5.17`).

- [ ] **Step 2: 找插入点**

运行: `cd /Users/auric/newmath && grep -n "HARD GATE — meta-capstone trivial-overlap" papers/bedc/scripts/prompts/phase_review.txt`
预期: 已存在的某 HARD GATE 段行号. 在该段 body 结束后 (下一个 `##` 标题前) 插入.

- [ ] **Step 3: 插入 G_taste_gate_feasibility 段**

插入下列内容到 phase_review.txt:

```
## HARD GATE — TasteGate feasibility (G_taste_gate_feasibility)

Any `theory_extension` target whose `notes.flavor` is `"human_chapter_extension"` MUST include a `taste_gate_feasibility` sub-object in `notes`, with five required fields all non-empty:

- `bhist_carrier_sketch`: one paragraph showing how X-tokens embed into BHist or a BHist-parameterized structure. If X requires an unboxable infinite parameter set or a non-BHist primitive, write `"fails"` and DROP the candidate.

- `conservativity_argument`: one paragraph showing that admitting X does not make any existing BEDC theorem unprovable, and that any new theorem provable in the extended system explicitly mentions X. Cite `\autoref{ch:ground-compiler-...}` where applicable.

- `no_hidden_input_argument`: one paragraph showing that every X-token is the recognized image of a finite event flow displayed from `\bzero, \bone`, in the sense of `\autoref{ch:ground-compiler-event-flow}`. If X needs an external oracle, a representation-only metadata row, or an unbounded parameter set, write `"fails"` and DROP.

- `round_trip_argument`: one paragraph showing how display readback composed with reconstruction is identity on X-tokens, in the sense of `\autoref{ch:ground-compiler-zeckendorf-safe-channel-encoding}`'s `flow_level_round_trip`. If display loses information, write `"fails"` and DROP.

- `layer_separation_argument`: one paragraph showing that X's source role (BHist material), channel role (composition rule), and display role (visible packet) do not collapse, in the sense of `\autoref{ch:ground-compiler-source-channel-layer-separation}`. If two of three roles are identified, write `"fails"` and DROP.

If all five arguments are present and non-`"fails"`, propose the candidate. If any is `"fails"`, do NOT propose. Record the dropped candidate in the round-level `rejected_candidates` list (transparency block schema below).

Candidates derived from capstone narrative follow the SAME gate as any other `human_chapter_extension`. No special path.

The next R-round implements `ChapterTasteGate X` as a real Lean instance with non-trivial bodies (no `Unit` / `True.intro` placeholders). This P-round's feasibility sketch is the basis for that implementation. If a candidate's sketch turns out wrong (R-round cannot build `ChapterTasteGate`), the chapter is rolled back via `git revert` in the next P-round.
```

- [ ] **Step 4: 提交**

```bash
cd /Users/auric/newmath
git add papers/bedc/scripts/prompts/phase_review.txt
git commit -m "phase_review.txt: add G_taste_gate_feasibility HARD GATE

每个 human_chapter_extension target 必须含 notes.taste_gate_feasibility,
5 个 required 字段各非空且不等于 'fails'. 实施 spec §4.2 / D1.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

---

## Task 12: phase_review.txt — G_capstone_stop_respect + transparency schema

**文件:**
- 修改: `papers/bedc/scripts/prompts/phase_review.txt`

- [ ] **Step 1: 在 Task 11 段后追加**

```
## HARD GATE — capstone STOP marker respect (G_capstone_stop_respect)

Before adding any candidate to `proposed_candidates` whose `source_capstone` points to a real capstone file, identify the **nearest containing block** of the candidate's `source_location` lines — the innermost `\section{...}` / `\subsection{...}` / `\paragraph{...}` whose body contains those lines (or the whole chapter if no such structure surrounds it).

Grep that block for any of:

- `SCHEMA-ONLY`
- `deferred to future`
- `not yet developed`
- `future development that does not yet exist`

If ANY of these appears in the surrounding block, the candidate MUST be placed in `deferred_candidates` (not `proposed_candidates`), with `stop_marker_text` quoting the exact STOP phrase observed.

Rationale: the user wrote these markers to defer formalization. The pipeline respects user intent. If user later removes the STOP marker, the candidate re-enters the proposal pool on the next P-round.

`bedc_ci.py audit` enforces this: proposing a STOP-region candidate fails the audit and causes round abort.

## Required transparency block in commit message body

Every P-round commit message body MUST include a fenced YAML block opened with `` ```transparency ``. Schema:

```
proposed_candidates:
  - name: <X>Up
    source_capstone: <theme-slug-or-null>
    source_location: papers/bedc/parts/visions/<theme>.tex:L<start>-L<end>
    taste_gate_feasibility:
      bhist_carrier_sketch: "<text>"
      conservativity_argument: "<text>"
      no_hidden_input_argument: "<text>"
      round_trip_argument: "<text>"
      layer_separation_argument: "<text>"

rejected_candidates:
  - concept: <name>
    source_capstone: <theme-slug-or-null>
    source_location: <file>:L<start>-L<end>
    failed_obligation: bhist_carrier_sketch | conservativity_argument | no_hidden_input_argument | round_trip_argument | layer_separation_argument
    rationale: "<one sentence>"

deferred_candidates:
  - concept: <name>
    source_capstone: <theme-slug-or-null>
    source_location: <file>:L<start>-L<end>
    stop_marker_text: "<quoted STOP phrase>"

implemented_targets:
  - name: <X>Up
    file: papers/bedc/parts/concrete_instances/<NN>_<slug>_namecert_construction.tex
    derivedfrom: ch:visions-<theme>   # optional, only when capstone-derived
```

`implemented_targets[].derivedfrom` 是可选字段. 当 chapter 由 capstone narrative 触发时填 `ch:visions-<theme>` (该 theme 必须真存在); audit `G_derived_from_traceability` 验证. 独立 horizon (与 capstone 无关) 省略此字段.

Missing transparency block: G_capstone_stop_respect 和 G_taste_gate_feasibility 无法 audit, 但 G_derived_from_traceability 也 skip — 这是可见性损失, 非 invariant 违反.
```

- [ ] **Step 2: 提交**

```bash
cd /Users/auric/newmath
git add papers/bedc/scripts/prompts/phase_review.txt
git commit -m "phase_review.txt: G_capstone_stop_respect + transparency YAML schema

AI 必须跳过任何 source_location 位于含 SCHEMA-ONLY / deferred-to-future
等 STOP marker 区域的 candidate, 放入 deferred_candidates 而非
proposed_candidates. 定义 commit body 必含的 YAML transparency block
(proposed / rejected / deferred / implemented). Spec §4.3 / D2 + §4.6.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

---

## Task 13: phase_revise.txt — commit transparency block 模板

**文件:**
- 修改: `papers/bedc/scripts/prompts/phase_revise.txt`

- [ ] **Step 1: 找插入点**

运行: `cd /Users/auric/newmath && grep -n "Step 6: Single combined commit\|^## Step" papers/bedc/scripts/prompts/phase_revise.txt | head`
预期: "Single combined commit" 段行号.

- [ ] **Step 2: 追加 commit transparency 模板**

在 `## Step 6: Single combined commit` 段既有模板之后追加:

```
### Required transparency block in commit body

Every P-round commit message body MUST contain a `` ```transparency `` fenced YAML block. Schema in phase_review.txt §"Required transparency block in commit message body". Populate from this round's work:

1. `proposed_candidates` — each candidate you considered AND proposed this round. Include full 5-field `taste_gate_feasibility`. `source_location` is the exact line range in the capstone where the concept was identified.
2. `rejected_candidates` — each candidate considered AND dropped due to TasteGate failure. Include `failed_obligation` and 1-sentence `rationale`.
3. `deferred_candidates` — each candidate skipped because the capstone region contains a STOP marker. Quote the exact `stop_marker_text` observed.
4. `implemented_targets` — each target actually committed this round. Include `file` path. Add optional `derivedfrom: ch:visions-<theme>` ONLY when the chapter was created in response to that capstone's narrative — the theme must reference a real `parts/visions/<theme>.tex`. Omit `derivedfrom` for independent horizons.

Example:

```
P<N>: <subject>

<body prose>

```transparency
proposed_candidates: []
rejected_candidates: []
deferred_candidates: []
implemented_targets:
  - name: ExampleUp
    file: papers/bedc/parts/concrete_instances/<NN>_example_namecert_construction.tex
    derivedfrom: ch:visions-some-theme
```

prompts: vN.M

Co-Authored-By: Codex <noreply@openai.com>
```

`bedc_ci.py audit` runs G_derived_from_traceability, G_capstone_stop_respect, and G_taste_gate_feasibility on this block. Audit failure = round abort.
```

- [ ] **Step 3: 提交**

```bash
cd /Users/auric/newmath
git add papers/bedc/scripts/prompts/phase_revise.txt
git commit -m "phase_revise.txt: commit transparency block 模板

Commit body 必含 YAML transparency block (proposed / rejected /
deferred / implemented), audit 解析后跑 3 个 commit-message-driven
gate. implemented_targets[].derivedfrom 是可选字段, 标记 chapter 是否
由 capstone narrative 触发.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

---

## Task 14: Phase 4 集成测试 in inter_hist_locality

**文件:**
- 只验证; 可能创建 `docs/superpowers/plans/2026-05-11-capstones-pipeline-validation.md`

- [ ] **Step 1: 确认 inter_hist_locality.tex 保留 SCHEMA-ONLY 标注**

运行: `cd /Users/auric/newmath && grep -cE "SCHEMA-ONLY|deferred to future" papers/bedc/parts/visions/inter_hist_locality.tex`
预期: ≥ 6 (匹配 spec §11.5 fixture).

- [ ] **Step 2: 跑 P-round**

```bash
cd /Users/auric/newmath
python3 papers/bedc/scripts/codex_revise.py 2>&1 | tee /tmp/p_round.log | tail -50
```

预期: codex P-round 产出. 用新 prompt 后, proposed target 应含 `taste_gate_feasibility` 分析, 任何 source_location 位于 inter_hist_locality SCHEMA-ONLY 区域的 candidate 应入 `deferred_candidates`.

- [ ] **Step 3: 验证 P-round commit**

```bash
cd /Users/auric/newmath
python3 lean4/scripts/bedc_ci.py audit 2>&1 | tail -30
```

预期: exit 0. 7 个新 gate 都通过:
- 任何 capstone-derived chapter 的 `derivedfrom` 解析到真 capstone
- 无 proposed candidate 在 STOP 区域
- 所有 proposed candidate 含完整 5 字段 feasibility
- 每日 rate 未超 cap
- 主题未饱和
- NN 重复 lint warn (现有 271/272/273 race) 但不 fail

- [ ] **Step 4: 写 validation 报告**

创建 `docs/superpowers/plans/2026-05-11-capstones-pipeline-validation.md`:

```markdown
# Phase 4 Validation: Capstones-Intuition Pipeline on inter_hist_locality

**日期:** <填入运行时间>
**Spec:** docs/superpowers/specs/2026-05-11-capstones-intuition-pipeline-spec.md
**Plan:** docs/superpowers/plans/2026-05-11-capstones-intuition-pipeline.md

## P-round 概况

- Round: P<...>
- Commit: <SHA>
- proposed_candidates 数: <count>
- rejected_candidates 数: <count>
- deferred_candidates 数: <count>
- implemented_targets 数: <count>

## Gate 实际行为

- G_taste_gate_feasibility: <PASS/FAIL/N-A>, <一句话>
- G_capstone_stop_respect: <PASS/FAIL/N-A>, <一句话>
- G_derived_from_traceability: <PASS/FAIL/N-A>, <一句话>
- G_emergency_brake: <PASS/FAIL/N-A>
- G_daily_rate: <PASS/FAIL/N-A>
- G_theme_saturation_enhanced: <PASS/FAIL/N-A>
- nn_duplicate_lint: <warn line 数>

## 成功标准

- [ ] 至少 1 个 deferred_candidates 来自 inter_hist_locality 的 SCHEMA-ONLY 区域
- [ ] 若有 chapter 被创建, 含 implemented_targets[].derivedfrom 指向 ch:visions-inter-hist-locality
- [ ] 所有 7 gate PASS (无 false positive / false negative) 或记录 failure mode

## 发现的问题 (若有)

<描述任何 gate misbehavior / false positive / false negative; 如需后续修复, 起 follow-up task>
```

由人工填表 (照 P-round 输出).

- [ ] **Step 5: 提交 validation note**

```bash
cd /Users/auric/newmath
git add docs/superpowers/plans/2026-05-11-capstones-pipeline-validation.md
git commit -m "Document Phase 4 validation for capstones-intuition pipeline

记录 inter_hist_locality fixture 上观察到的 gate 行为. 含 proposed /
rejected / deferred candidate 数与每个 gate 的 pass/fail 状态.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"
```

---

## 验证 summary

完成全部 14 task 后:

1. **36 unit tests** 通过 in `lean4/scripts/test_capstones_pipeline_gates.py`, 覆盖 6 audit + 1 lint + transparency parser + STOP helper (Task 1-9)
2. `bedc_ci.py audit` 自动跑 7 个新 gate, 触发条件正确 (Task 10):
   - 3 个 commit-message gate 仅当 HEAD 是 P-round 时 fire
   - 3 个 filesystem-state gate 仅当 HEAD 加新顶层 chapter 时 fire
   - 1 个 warn-only lint 总是跑
3. phase_review.txt 引导 AI 填 transparency block + 跑 TasteGate feasibility + 尊重 STOP marker (Task 11-12)
4. phase_revise.txt 引导 AI 在 commit body 写 transparency block + 选填 `implemented_targets[].derivedfrom` (Task 13)
5. Phase 4 集成测试 in inter_hist_locality 验证端到端 (Task 14)
6. **codex_revise.py / preamble.tex 不动** — phase VERIFY 已调 audit, 新 gate 自动 fire; traceability 走 commit body 而非 LaTeX 宏, 保持 PDF 干净

总计: **3 文件修改 + 1 文件创建 = ~310 实施行 + ~300 测试行**. **14 个原子 commit**.

Task 14 成功 → v5 spec 可运行.
Task 14 失败 → 调 phase_review.txt 措辞, 不回滚 audit 代码.
