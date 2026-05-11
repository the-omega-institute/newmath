# Pipeline Framework V1 Foundation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** 实现 V1 substrate library (≤1000 LOC, 5 component) + bedc_gates package + 把 `tools/sync_with_auto_dev.py` 重写成首个 production pipeline. 这是后续迁移 codex_formalize / codex_revise 的 foundation; 单独 ship 就能用 sync pipeline 替代旧脚本.

**Architecture:** subprocess supervisor 模型 (不用 asyncio). substrate 提供 Pipeline + Context + WorktreeMgr + CodexCLI + GateRunner + GitOps 五个 component; pipeline 是独立 python 文件 import substrate; bedc_gates 跟 substrate 同级独立 package 装 BEDC-specific gate. Phase 1 是 spike (用 codex_formalize 当 stress test 定义 substrate API), Phase 2 实现 substrate (TDD), Phase 3 bedc_gates, Phase 4 sync pipeline 跑通.

**Tech Stack:** Python 3.10+ stdlib only (subprocess, pathlib, dataclasses, logging, typing, contextlib). pytest for testing. git CLI + codex CLI as external tools. 不引入第三方依赖.

---

## Prerequisites

- 在 newmath repo 的 `feat-pipeline-runner` 分支 (从 `dev` 起): `git checkout dev && git pull && git checkout -b feat-pipeline-runner`
- `python3 --version` ≥ 3.10
- `pytest --version` 可运行 (`pip install pytest` 如缺)
- `codex --version` 可运行, `codex login` 已完成
- 读过 design doc: `~/.gstack/projects/the-omega-institute-newmath/auric-auto-dev-design-20260511-210724.md`
- 读过 test plan: `~/.gstack/projects/the-omega-institute-newmath/auric-auto-dev-eng-review-test-plan-20260511-230149.md`

## File Structure

每个文件单一职责. 大小硬指标见各 Task.

```
newmath_substrate/
├── __init__.py            # exports
├── pipeline.py            # Pipeline ABC + Context dataclass (~150 LOC)
├── worktree_mgr.py        # WorktreeMgr class (~180 LOC)
├── codex_cli.py           # CodexCLI class + typed exceptions (~150 LOC)
├── gate_runner.py         # GateRunner class + Gate protocol (~80 LOC)
├── git_ops.py             # GitOps class (~220 LOC, hard cap)

bedc_gates/
├── __init__.py            # exports
├── base.py                # GateResult dataclass + Gate Protocol re-export (~30 LOC)
├── lake_build.py          # LakeBuild gate (~50 LOC)
├── axiom_purity.py        # AxiomPurity gate (~50 LOC)
├── bedc_ci_audit.py       # BedcCiAudit gate (~50 LOC)
├── check_math_env.py      # CheckMathEnv gate (~30 LOC)
├── check_tex_size.py      # CheckTexSize gate (~30 LOC)

pipelines/
├── __init__.py            # (empty marker)
├── sync.py                # sync pipeline file (≤150 LOC, 含 import + docstring)

tests/
├── substrate/
│   ├── test_pipeline.py
│   ├── test_worktree_mgr.py
│   ├── test_codex_cli.py
│   ├── test_gate_runner.py
│   ├── test_git_ops.py
├── bedc_gates/
│   ├── test_lake_build.py
│   ├── test_axiom_purity.py
│   ├── test_bedc_ci_audit.py
├── pipelines/
│   ├── test_sync.py        # integration smoke test for sync pipeline

scripts/
├── substrate_contract_test.py  # golden tests, 每个 substrate component ≥3 golden

docs/substrate_api.md      # Phase 1 spike output
pipelines/codex_formalize.py.sketch  # Phase 1 spike output, not executable
```

V1 substrate 总 LOC 目标: 150 + 180 + 150 + 80 + 220 = 780 LOC, 留 220 buffer 到硬指标 1000.

---

## Phase 1: Spike — 用 codex_formalize 定义 substrate API

Phase 1 是**调查阶段**, 不是 TDD. 目标是从 3748 行的 codex_formalize.py 里抽出"如果有完美 substrate, 我会怎么调用它"的 sketch + 显式 substrate API 列表.

### Task 1: Inventory codex_formalize.py

**Files:**
- Read: `lean4/scripts/codex_formalize.py`
- Create: `docs/superpowers/spike-notes/codex_formalize_inventory.md`

- [ ] **Step 1: 通读 codex_formalize.py, 把它分类为 6 个区域**

打开 `lean4/scripts/codex_formalize.py`. 边读边标记每个函数 / class / 大段代码块的归属:

1. **WORKTREE** (git worktree 创建 / cleanup / rebase / merge)
2. **CODEX** (`codex exec` 调用 / prompt 构造 / stderr 解析 / timeout)
3. **GATE** (lake build / axiom-purity / bedc_ci audit 调用 + 结果解析)
4. **TASK_DISCOVERY** (读 BOARD.md / git log / 找下一个 task)
5. **PIPELINE_LOGIC** (除以上 4 类之外, 业务规则: 哪些 task 跳过 / 哪个 prompt 配哪种 task / commit message 格式)
6. **CRUFT** (debug print / 实验代码 / 注释 / 已废弃)

- [ ] **Step 2: 写 inventory 文档**

创建 `docs/superpowers/spike-notes/codex_formalize_inventory.md`:

```markdown
# codex_formalize.py Inventory

Total LOC: 3748 (verify with `wc -l lean4/scripts/codex_formalize.py`)

## WORKTREE region (~X LOC)
- `function_name_1` (line A-B): 做 X
- `function_name_2` (line C-D): 做 Y
- ... (列完)

## CODEX region (~X LOC)
- ... (同)

## GATE region (~X LOC)
- ...

## TASK_DISCOVERY region (~X LOC)
- ...

## PIPELINE_LOGIC region (~X LOC)
- ... (这块是 pipeline-specific, 不进 substrate)

## CRUFT (~X LOC)
- ...

## 总结
- 进 substrate (WORKTREE + CODEX + GATE 调用面 + GitOps): ~X LOC
- 留 pipeline (TASK_DISCOVERY + PIPELINE_LOGIC): ~Y LOC
- 删除 (CRUFT): ~Z LOC
```

- [ ] **Step 3: Commit inventory**

```bash
git add docs/superpowers/spike-notes/codex_formalize_inventory.md
git commit -m "spike: inventory codex_formalize.py regions for substrate extraction"
```

### Task 2: Write substrate_api.md

**Files:**
- Create: `docs/substrate_api.md`

- [ ] **Step 1: 列出每个 component 的 method signature**

基于 inventory, 写 `docs/substrate_api.md`. 每个 method 给具体类型签名 + 一行说明 + 哪个 inventory 区域来的:

```markdown
# Substrate API v1

## newmath_substrate.WorktreeMgr

```python
class WorktreeMgr:
    def __init__(self, repo_root: Path, worktree_root: Path = Path("/tmp/newmath-worktrees")): ...

    def create(self, branch_name: str, base_branch: str) -> Path:
        """创建 worktree, 返回 worktree 绝对路径. 名字冲突 → raise WorktreeNameClash."""

    def cleanup(self, wt_path: Path) -> None:
        """git worktree remove + 强制 prune. 失败抛 WorktreeCleanupFailed."""

    def dirty_restart_skip(self, wt_path: Path) -> bool:
        """如果存在 .runner-lock 文件 → True (skip); 否则 False."""

    def list_dirty(self) -> list[Path]:
        """返回所有标 dirty 的 worktree path. supervisor 启动时调."""
```

## newmath_substrate.CodexCLI

```python
class CodexCLI:
    def __init__(self, wt_path: Path): ...

    def exec(self, prompt: str, timeout: int = 600) -> CodexResult:
        """运行 codex exec --dangerously-bypass... -C <wt>.
        Raises: CodexAuth (login 失败) / CodexTimeout / CodexEmpty / CodexUnknown."""
```

(以此类推, 把 5 个 substrate component + bedc_gates 5 个 gate class 全列出)
```

- [ ] **Step 2: 标 baseline counts (API churn budget anchor)**

在 `docs/substrate_api.md` 末尾加:

```markdown
## Baseline (V1 spike-locked)

- Total components: 5 (Pipeline+Context, WorktreeMgr, CodexCLI, GateRunner, GitOps)
- Total public methods: <count, e.g. 18>
- Estimated total LOC: <sum from file structure, e.g. 780>

API churn budget: 后续步骤迁移 codex_formalize / codex_revise 中, 总 public method 数 OR 总 LOC 增量 >30% 触发 "停下重新评估" review checkpoint.
```

- [ ] **Step 3: Commit substrate_api.md**

```bash
git add docs/substrate_api.md
git commit -m "spike: lock substrate API surface from codex_formalize inventory"
```

### Task 3: Write codex_formalize.py.sketch

**Files:**
- Create: `pipelines/codex_formalize.py.sketch`

- [ ] **Step 1: 写 sketch (≤ 250 LOC), 假设 substrate 已存在**

创建 `pipelines/codex_formalize.py.sketch`. 这文件**不**可执行 (substrate 不存在), 是参考实现:

```python
"""codex_formalize pipeline sketch (Phase 1 spike output).

NOT EXECUTABLE: substrate 还不存在. 用 .sketch 后缀避免被当成真 pipeline.
作用: stress-test substrate API 是否够装下真实 codex_formalize 业务逻辑.
"""

from pathlib import Path
from newmath_substrate import Pipeline, Context, CodexCLI, GateRunner, GitOps
from bedc_gates import LakeBuild, AxiomPurity, BedcCiAudit


class CodexFormalizePipeline(Pipeline):
    name = "codex-formalize"
    base_branch = "codex-auto-dev"
    concurrency = 3  # supervisor spawn 最多 3 个 worker

    def discover_tasks(self) -> list[dict]:
        """读 BOARD.md / git log, 返回未完成的 Lean formalization 任务列表.
        每个 dict: {id: str, title: str, lean_target: str, scope: str}
        """
        board_path = self.ctx.repo_root / "tools/bedc-deep/BOARD.md"
        # ... 读 board, parse, 过滤已 done, 返回 list

    def run_task(self, task: dict) -> None:
        """单 task 执行. 同步函数 (subprocess supervisor 模型).
        异常会被 supervisor 捕获 + log + 跳过此任务."""
        wt = self.ctx.worktree_mgr.create(
            branch_name=f"worker-formalize-{task['id']}",
            base_branch=self.base_branch,
        )
        try:
            # 构造 prompt
            prompt_template = (Path(__file__).parent / "prompts/formalize.txt").read_text()
            prompt = prompt_template.format(
                task=task,
                manifest=self.ctx.bedc_manifest,  # ctx 注入 BEDC manifest
            )

            # 跑 codex
            codex = CodexCLI(wt)
            result = codex.exec(prompt, timeout=600)
            self.ctx.logger.info(f"codex completed for task {task['id']}: {result.summary}")

            # 跑 gate
            gates = [LakeBuild(), AxiomPurity(), BedcCiAudit()]
            GateRunner(gates).require_pass(wt)

            # merge
            git_ops = GitOps(wt)
            git_ops.merge_to_base_with_retry(
                base_branch=self.base_branch,
                message=f"codex-formalize: {task['title']} ({task['id']})",
            )
        finally:
            self.ctx.worktree_mgr.cleanup(wt)
```

(实际 sketch 比这更长 — 加 retry 策略 / 错误分类 / 跳过条件 / commit message 格式 / BOARD.md 写回. 目标 ~200 LOC.)

- [ ] **Step 2: Count LOC + 校验 ≤ 250**

```bash
wc -l pipelines/codex_formalize.py.sketch
```

Expected: ≤ 250. 超了说明 PIPELINE_LOGIC 区域还有该进 substrate 的代码, 回头加. 反过来 < 100 行可能太薄 (substrate 装太多 BEDC-specific 假设).

- [ ] **Step 3: Commit sketch**

```bash
git add pipelines/codex_formalize.py.sketch
git commit -m "spike: codex_formalize sketch as substrate API stress-test"
```

---

## Phase 2: V1 Substrate Implementation (TDD)

每个 Task = 一个 TDD cycle (写测试 → 看失败 → 写实现 → 看通过 → 提交).

### Task 4: Repo scaffolding

**Files:**
- Create: `newmath_substrate/__init__.py`
- Create: `newmath_substrate/exceptions.py`
- Create: `tests/substrate/__init__.py`
- Create: `tests/conftest.py`

- [ ] **Step 1: 创建包目录 + 空 __init__**

```bash
mkdir -p newmath_substrate tests/substrate tests/bedc_gates tests/pipelines bedc_gates pipelines
touch newmath_substrate/__init__.py tests/substrate/__init__.py tests/__init__.py tests/bedc_gates/__init__.py tests/pipelines/__init__.py
```

- [ ] **Step 2: 写 exceptions 模块 (substrate 全局错误类型)**

创建 `newmath_substrate/exceptions.py`:

```python
"""Substrate 通用异常类型.

设计原则: 异常按 failure domain 分类, pipeline 可以按需要 catch."""


class SubstrateError(Exception):
    """所有 substrate 错误的基类."""


class WorktreeError(SubstrateError):
    """Worktree 操作相关."""


class WorktreeNameClash(WorktreeError):
    """请求的 worktree 名字已存在."""


class WorktreeCleanupFailed(WorktreeError):
    """git worktree remove 失败."""


class CodexError(SubstrateError):
    """codex CLI 调用相关."""


class CodexAuth(CodexError):
    """codex 未登录 / token 失效."""


class CodexTimeout(CodexError):
    """codex exec 超过 timeout."""


class CodexEmpty(CodexError):
    """codex 返回空 / 没输出."""


class CodexUnknown(CodexError):
    """未分类 codex 错误."""


class GateFailed(SubstrateError):
    """gate 不通过. detail 在 .result 字段."""

    def __init__(self, gate_name: str, exit_code: int, stderr: str):
        self.gate_name = gate_name
        self.exit_code = exit_code
        self.stderr = stderr
        super().__init__(f"Gate {gate_name} failed (exit={exit_code}): {stderr[:200]}")


class GateTimeout(SubstrateError):
    """gate 超过 timeout."""


class GitOpsError(SubstrateError):
    """git operation 失败."""


class GitOpsPushRejected(GitOpsError):
    """push 被远端拒绝 (non-fast-forward)."""


class GitOpsMergeConflict(GitOpsError):
    """merge 有冲突."""
```

- [ ] **Step 3: 写 conftest.py (pytest 共享 fixture)**

创建 `tests/conftest.py`:

```python
"""pytest 共享 fixture, 提供临时 repo 给 substrate test."""

import subprocess
from pathlib import Path
import pytest


@pytest.fixture
def temp_repo(tmp_path: Path) -> Path:
    """初始化一个空 git repo 在 tmp_path/repo, 返回 path.
    有一个 initial commit + main + dev 两个 branch."""
    repo = tmp_path / "repo"
    repo.mkdir()
    subprocess.run(["git", "init", "-q", "-b", "main"], cwd=repo, check=True)
    subprocess.run(["git", "config", "user.email", "test@test"], cwd=repo, check=True)
    subprocess.run(["git", "config", "user.name", "test"], cwd=repo, check=True)
    (repo / "README.md").write_text("# test\n")
    subprocess.run(["git", "add", "."], cwd=repo, check=True)
    subprocess.run(["git", "commit", "-q", "-m", "initial"], cwd=repo, check=True)
    subprocess.run(["git", "branch", "dev"], cwd=repo, check=True)
    return repo


@pytest.fixture
def temp_worktree_root(tmp_path: Path) -> Path:
    """临时 worktree root, 隔离每个测试."""
    root = tmp_path / "worktrees"
    root.mkdir()
    return root
```

- [ ] **Step 4: 验证 pytest 能跑 (空集合)**

```bash
cd /Users/auric/newmath
pytest tests/ -v
```

Expected: 0 test collected, 退出码 5 (pytest "no tests" code). 不报错说明 collection 正常.

- [ ] **Step 5: Commit scaffolding**

```bash
git add newmath_substrate/ tests/ bedc_gates/ pipelines/
git commit -m "feat(substrate): scaffold package structure + exceptions + conftest"
```

### Task 5: WorktreeMgr.create() basic

**Files:**
- Create: `tests/substrate/test_worktree_mgr.py`
- Create: `newmath_substrate/worktree_mgr.py`

- [ ] **Step 1: 写失败测试**

创建 `tests/substrate/test_worktree_mgr.py`:

```python
"""WorktreeMgr tests."""

import subprocess
from pathlib import Path
import pytest
from newmath_substrate.worktree_mgr import WorktreeMgr


def test_create_basic(temp_repo: Path, temp_worktree_root: Path):
    """create() 返回 path, path 存在, 是 git worktree."""
    mgr = WorktreeMgr(repo_root=temp_repo, worktree_root=temp_worktree_root)
    wt = mgr.create(branch_name="feature/test", base_branch="dev")

    assert wt.exists()
    assert wt.is_dir()
    assert (wt / ".git").exists()  # worktree 有 .git file

    # 是 git worktree, 不是普通 dir
    result = subprocess.run(
        ["git", "worktree", "list"], cwd=temp_repo, capture_output=True, text=True
    )
    assert str(wt) in result.stdout
```

- [ ] **Step 2: 运行测试看失败**

```bash
pytest tests/substrate/test_worktree_mgr.py::test_create_basic -v
```

Expected: `ImportError: cannot import name 'WorktreeMgr'` 或 `ModuleNotFoundError`.

- [ ] **Step 3: 写最小实现**

创建 `newmath_substrate/worktree_mgr.py`:

```python
"""Git worktree lifecycle management."""

import subprocess
from pathlib import Path
from newmath_substrate.exceptions import WorktreeNameClash, WorktreeCleanupFailed


class WorktreeMgr:
    """每个 task 一个 worktree, 隔离 git state."""

    def __init__(self, repo_root: Path, worktree_root: Path):
        self.repo_root = repo_root
        self.worktree_root = worktree_root
        self.worktree_root.mkdir(parents=True, exist_ok=True)

    def create(self, branch_name: str, base_branch: str) -> Path:
        """创建 worktree at worktree_root / <safe-branch-name>.
        分支名带 / 替换成 -, 避免文件路径问题."""
        safe_name = branch_name.replace("/", "-")
        wt_path = self.worktree_root / safe_name

        if wt_path.exists():
            raise WorktreeNameClash(f"worktree {wt_path} already exists")

        subprocess.run(
            ["git", "worktree", "add", "-b", branch_name, str(wt_path), base_branch],
            cwd=self.repo_root,
            check=True,
            capture_output=True,
        )
        return wt_path
```

- [ ] **Step 4: 跑测试看通过**

```bash
pytest tests/substrate/test_worktree_mgr.py::test_create_basic -v
```

Expected: 1 passed.

- [ ] **Step 5: Commit**

```bash
git add tests/substrate/test_worktree_mgr.py newmath_substrate/worktree_mgr.py
git commit -m "feat(substrate): WorktreeMgr.create basic"
```

### Task 6: WorktreeMgr.cleanup()

**Files:**
- Modify: `tests/substrate/test_worktree_mgr.py`
- Modify: `newmath_substrate/worktree_mgr.py`

- [ ] **Step 1: 加失败测试**

在 `tests/substrate/test_worktree_mgr.py` 末尾追加:

```python
def test_cleanup_removes_worktree(temp_repo: Path, temp_worktree_root: Path):
    mgr = WorktreeMgr(repo_root=temp_repo, worktree_root=temp_worktree_root)
    wt = mgr.create(branch_name="feature/cleanup", base_branch="dev")
    assert wt.exists()

    mgr.cleanup(wt)

    assert not wt.exists()
    # git worktree list 不再包含它
    result = subprocess.run(
        ["git", "worktree", "list"], cwd=temp_repo, capture_output=True, text=True
    )
    assert str(wt) not in result.stdout
```

- [ ] **Step 2: 跑测试看失败**

```bash
pytest tests/substrate/test_worktree_mgr.py::test_cleanup_removes_worktree -v
```

Expected: `AttributeError: 'WorktreeMgr' object has no attribute 'cleanup'`.

- [ ] **Step 3: 加实现**

在 `newmath_substrate/worktree_mgr.py` 的 `WorktreeMgr` class 内追加:

```python
    def cleanup(self, wt_path: Path) -> None:
        """git worktree remove. force=True 因为 worker 完成后可能还有 untracked file."""
        result = subprocess.run(
            ["git", "worktree", "remove", "--force", str(wt_path)],
            cwd=self.repo_root,
            capture_output=True,
            text=True,
        )
        if result.returncode != 0:
            raise WorktreeCleanupFailed(
                f"cleanup {wt_path} failed (exit={result.returncode}): {result.stderr}"
            )
```

- [ ] **Step 4: 跑测试**

```bash
pytest tests/substrate/test_worktree_mgr.py -v
```

Expected: 2 passed.

- [ ] **Step 5: Commit**

```bash
git add tests/substrate/test_worktree_mgr.py newmath_substrate/worktree_mgr.py
git commit -m "feat(substrate): WorktreeMgr.cleanup"
```

### Task 7: WorktreeMgr.create() name collision

**Files:**
- Modify: `tests/substrate/test_worktree_mgr.py`

- [ ] **Step 1: 加测试: 同名 create 二次抛 WorktreeNameClash**

追加到 `tests/substrate/test_worktree_mgr.py`:

```python
from newmath_substrate.exceptions import WorktreeNameClash


def test_create_name_clash(temp_repo: Path, temp_worktree_root: Path):
    mgr = WorktreeMgr(repo_root=temp_repo, worktree_root=temp_worktree_root)
    mgr.create(branch_name="feature/clash", base_branch="dev")

    with pytest.raises(WorktreeNameClash):
        mgr.create(branch_name="feature/clash", base_branch="dev")
```

- [ ] **Step 2: 跑测试看通过 (impl 已经有 check)**

```bash
pytest tests/substrate/test_worktree_mgr.py::test_create_name_clash -v
```

Expected: passed (Task 5 已经实现了 if wt_path.exists() raise).

- [ ] **Step 3: Commit**

```bash
git add tests/substrate/test_worktree_mgr.py
git commit -m "test(substrate): WorktreeMgr.create raises on name collision"
```

### Task 8: WorktreeMgr.dirty_restart_skip() + list_dirty()

**Files:**
- Modify: `tests/substrate/test_worktree_mgr.py`
- Modify: `newmath_substrate/worktree_mgr.py`

- [ ] **Step 1: 加失败测试**

追加:

```python
def test_dirty_restart_skip_no_lock(temp_repo: Path, temp_worktree_root: Path):
    mgr = WorktreeMgr(repo_root=temp_repo, worktree_root=temp_worktree_root)
    wt = mgr.create(branch_name="feature/dirty-test", base_branch="dev")

    # 没有 .runner-lock → 不 skip
    assert mgr.dirty_restart_skip(wt) is False


def test_dirty_restart_skip_with_lock(temp_repo: Path, temp_worktree_root: Path):
    mgr = WorktreeMgr(repo_root=temp_repo, worktree_root=temp_worktree_root)
    wt = mgr.create(branch_name="feature/dirty-test2", base_branch="dev")

    (wt / ".runner-lock").write_text("worker-pid: 12345")

    # 有 .runner-lock → skip (上次 crash 留下来的)
    assert mgr.dirty_restart_skip(wt) is True


def test_list_dirty_returns_locked_worktrees(temp_repo: Path, temp_worktree_root: Path):
    mgr = WorktreeMgr(repo_root=temp_repo, worktree_root=temp_worktree_root)
    wt1 = mgr.create(branch_name="feature/dirty-1", base_branch="dev")
    wt2 = mgr.create(branch_name="feature/dirty-2", base_branch="dev")
    (wt1 / ".runner-lock").write_text("worker-pid: 1")
    # wt2 没有 lock

    dirty = mgr.list_dirty()
    assert wt1 in dirty
    assert wt2 not in dirty
```

- [ ] **Step 2: 跑测试看失败**

```bash
pytest tests/substrate/test_worktree_mgr.py -v
```

Expected: 3 new test fail with `AttributeError`.

- [ ] **Step 3: 加实现**

在 `newmath_substrate/worktree_mgr.py` 的 `WorktreeMgr` class 内追加:

```python
    LOCK_FILE = ".runner-lock"

    def dirty_restart_skip(self, wt_path: Path) -> bool:
        """检测残留 lock 文件. supervisor 重启时调用这个跳过 in-flight 任务."""
        return (wt_path / self.LOCK_FILE).exists()

    def list_dirty(self) -> list[Path]:
        """扫 worktree_root, 返回所有带 .runner-lock 的 path."""
        if not self.worktree_root.exists():
            return []
        return [
            wt for wt in self.worktree_root.iterdir()
            if wt.is_dir() and (wt / self.LOCK_FILE).exists()
        ]
```

- [ ] **Step 4: 跑测试**

```bash
pytest tests/substrate/test_worktree_mgr.py -v
```

Expected: 5 passed (前面 2 + 这次新加 3).

- [ ] **Step 5: Commit**

```bash
git add tests/substrate/test_worktree_mgr.py newmath_substrate/worktree_mgr.py
git commit -m "feat(substrate): WorktreeMgr.dirty_restart_skip + list_dirty"
```

### Task 9: WorktreeMgr LOC sanity check

**Files:**
- Read: `newmath_substrate/worktree_mgr.py`

- [ ] **Step 1: 检查 LOC**

```bash
wc -l newmath_substrate/worktree_mgr.py
```

Expected: ≤ 180 LOC. 超了 → 抽 helper 或重新看 method 是否过粒度.

- [ ] **Step 2: 如超标, 提交一次 refactor commit (否则跳过)**

仅在 LOC 超标时, refactor + commit. 否则进 Task 10.

---

### Task 10: CodexCLI.exec() happy path

**Files:**
- Create: `tests/substrate/test_codex_cli.py`
- Create: `newmath_substrate/codex_cli.py`

- [ ] **Step 1: 写失败测试 (用 monkeypatch mock subprocess)**

```python
"""CodexCLI tests, mocks codex binary at subprocess level."""

from pathlib import Path
import subprocess
import pytest
from newmath_substrate.codex_cli import CodexCLI, CodexResult


def test_exec_happy_path(monkeypatch, tmp_path: Path):
    """codex exec 成功 → 返回 CodexResult."""
    calls = []

    class FakeCompleted:
        returncode = 0
        stdout = "All good\n"
        stderr = ""

    def fake_run(cmd, **kwargs):
        calls.append(cmd)
        return FakeCompleted()

    monkeypatch.setattr(subprocess, "run", fake_run)

    cli = CodexCLI(wt_path=tmp_path)
    result = cli.exec(prompt="do the thing", timeout=600)

    assert isinstance(result, CodexResult)
    assert result.exit_code == 0
    assert "All good" in result.stdout
    # 验证调用 cmd 含必需 flag
    assert "codex" in calls[0][0]
    assert "exec" in calls[0]
    assert "--dangerously-bypass-approvals-and-sandbox" in calls[0]
    assert "-C" in calls[0]
    assert str(tmp_path) in calls[0]
```

- [ ] **Step 2: 跑测试看失败**

```bash
pytest tests/substrate/test_codex_cli.py::test_exec_happy_path -v
```

Expected: ImportError.

- [ ] **Step 3: 写实现**

```python
"""codex CLI wrapper."""

import subprocess
from dataclasses import dataclass
from pathlib import Path
from newmath_substrate.exceptions import (
    CodexAuth, CodexTimeout, CodexEmpty, CodexUnknown,
)


@dataclass
class CodexResult:
    exit_code: int
    stdout: str
    stderr: str

    @property
    def summary(self) -> str:
        """First 200 chars of stdout, for log."""
        return self.stdout[:200].replace("\n", " ").strip()


class CodexCLI:
    """每个 CodexCLI 绑定一个 worktree (codex 在那 wt 里跑)."""

    def __init__(self, wt_path: Path):
        self.wt_path = wt_path

    def exec(self, prompt: str, timeout: int = 600) -> CodexResult:
        """运行 codex exec --dangerously-bypass-approvals-and-sandbox -C <wt> <prompt>.

        Raises:
            CodexAuth: 未登录或 token 失效
            CodexTimeout: 超过 timeout 秒
            CodexEmpty: 返回 stdout 为空
            CodexUnknown: 未分类错误
        """
        cmd = [
            "codex", "exec",
            "--dangerously-bypass-approvals-and-sandbox",
            "-C", str(self.wt_path),
            prompt,
        ]
        try:
            result = subprocess.run(
                cmd, capture_output=True, text=True, timeout=timeout,
            )
        except subprocess.TimeoutExpired as e:
            raise CodexTimeout(f"codex timed out after {timeout}s") from e

        if result.returncode != 0:
            self._classify_error(result.stderr)

        if not result.stdout.strip():
            raise CodexEmpty(f"codex returned empty stdout. stderr: {result.stderr[:200]}")

        return CodexResult(
            exit_code=result.returncode,
            stdout=result.stdout,
            stderr=result.stderr,
        )

    def _classify_error(self, stderr: str) -> None:
        """按 stderr 关键字抛分类异常."""
        lower = stderr.lower()
        if any(k in lower for k in ["auth", "login", "unauthorized", "api key"]):
            raise CodexAuth(f"codex auth failed: {stderr[:200]}")
        raise CodexUnknown(f"codex failed: {stderr[:200]}")
```

- [ ] **Step 4: 跑测试**

```bash
pytest tests/substrate/test_codex_cli.py -v
```

Expected: 1 passed.

- [ ] **Step 5: Commit**

```bash
git add tests/substrate/test_codex_cli.py newmath_substrate/codex_cli.py
git commit -m "feat(substrate): CodexCLI.exec happy path"
```

### Task 11: CodexCLI error classification

**Files:**
- Modify: `tests/substrate/test_codex_cli.py`

- [ ] **Step 1: 加 4 个 error path 测试**

```python
from newmath_substrate.exceptions import CodexAuth, CodexTimeout, CodexEmpty, CodexUnknown


def test_exec_auth_error(monkeypatch, tmp_path: Path):
    class FakeCompleted:
        returncode = 1
        stdout = ""
        stderr = "Error: authentication failed. Run `codex login`."

    monkeypatch.setattr(subprocess, "run", lambda cmd, **kw: FakeCompleted())

    cli = CodexCLI(wt_path=tmp_path)
    with pytest.raises(CodexAuth, match="authentication"):
        cli.exec(prompt="x")


def test_exec_timeout(monkeypatch, tmp_path: Path):
    def fake_run(cmd, **kwargs):
        raise subprocess.TimeoutExpired(cmd, timeout=600)

    monkeypatch.setattr(subprocess, "run", fake_run)

    cli = CodexCLI(wt_path=tmp_path)
    with pytest.raises(CodexTimeout):
        cli.exec(prompt="x", timeout=600)


def test_exec_empty_stdout(monkeypatch, tmp_path: Path):
    class FakeCompleted:
        returncode = 0
        stdout = "   \n  "  # whitespace only
        stderr = ""

    monkeypatch.setattr(subprocess, "run", lambda cmd, **kw: FakeCompleted())

    cli = CodexCLI(wt_path=tmp_path)
    with pytest.raises(CodexEmpty):
        cli.exec(prompt="x")


def test_exec_unknown_error(monkeypatch, tmp_path: Path):
    class FakeCompleted:
        returncode = 1
        stdout = ""
        stderr = "something weird happened"

    monkeypatch.setattr(subprocess, "run", lambda cmd, **kw: FakeCompleted())

    cli = CodexCLI(wt_path=tmp_path)
    with pytest.raises(CodexUnknown):
        cli.exec(prompt="x")
```

- [ ] **Step 2: 跑测试看通过 (impl 已经覆盖)**

```bash
pytest tests/substrate/test_codex_cli.py -v
```

Expected: 5 passed.

- [ ] **Step 3: Commit**

```bash
git add tests/substrate/test_codex_cli.py
git commit -m "test(substrate): CodexCLI error classification cases"
```

---

### Task 12: GateRunner + Gate Protocol

**Files:**
- Create: `tests/substrate/test_gate_runner.py`
- Create: `newmath_substrate/gate_runner.py`

- [ ] **Step 1: 写失败测试 (跑两个 fake gate, 一过一失败)**

```python
"""GateRunner tests."""

from pathlib import Path
import pytest
from newmath_substrate.gate_runner import GateRunner, GateResult
from newmath_substrate.exceptions import GateFailed


class FakeGate:
    """测试用 Gate, 返回固定 result."""
    def __init__(self, name: str, exit_code: int, stderr: str = ""):
        self.name = name
        self._exit = exit_code
        self._stderr = stderr

    def __call__(self, wt: Path) -> GateResult:
        return GateResult(name=self.name, exit_code=self._exit, stderr=self._stderr)


def test_require_pass_all_succeed(tmp_path: Path):
    gates = [FakeGate("g1", 0), FakeGate("g2", 0)]
    runner = GateRunner(gates)
    # 不抛 = pass
    runner.require_pass(tmp_path)


def test_require_pass_fail_fast(tmp_path: Path):
    """第一个 gate 失败, 第二个不该跑."""
    second_gate_called = []
    class TrackingGate(FakeGate):
        def __call__(self, wt):
            second_gate_called.append(True)
            return super().__call__(wt)

    g1 = FakeGate("g1", 1, stderr="lake build failed")
    g2 = TrackingGate("g2", 0)

    runner = GateRunner([g1, g2])
    with pytest.raises(GateFailed) as exc_info:
        runner.require_pass(tmp_path)

    assert exc_info.value.gate_name == "g1"
    assert "lake build failed" in exc_info.value.stderr
    assert second_gate_called == []  # g2 没跑
```

- [ ] **Step 2: 跑测试看失败**

```bash
pytest tests/substrate/test_gate_runner.py -v
```

Expected: ImportError.

- [ ] **Step 3: 写实现**

```python
"""Gate composition runner."""

from dataclasses import dataclass
from pathlib import Path
from typing import Protocol
from newmath_substrate.exceptions import GateFailed


@dataclass
class GateResult:
    name: str
    exit_code: int
    stderr: str = ""

    @property
    def passed(self) -> bool:
        return self.exit_code == 0


class Gate(Protocol):
    """Gate 协议: callable(wt: Path) -> GateResult."""
    name: str

    def __call__(self, wt: Path) -> GateResult: ...


class GateRunner:
    """顺序跑 gate, fail-fast on first failure.

    V1 没 per-gate timeout (列入 Open Issue, 见 design doc T5).
    """

    def __init__(self, gates: list[Gate]):
        self.gates = gates

    def require_pass(self, wt: Path) -> None:
        """跑所有 gate, 任何一个 raise GateFailed."""
        for gate in self.gates:
            result = gate(wt)
            if not result.passed:
                raise GateFailed(
                    gate_name=result.name,
                    exit_code=result.exit_code,
                    stderr=result.stderr,
                )
```

- [ ] **Step 4: 跑测试**

```bash
pytest tests/substrate/test_gate_runner.py -v
```

Expected: 2 passed.

- [ ] **Step 5: Commit**

```bash
git add tests/substrate/test_gate_runner.py newmath_substrate/gate_runner.py
git commit -m "feat(substrate): GateRunner + Gate protocol"
```

---

### Task 13: GitOps.fetch_and_merge() basic

**Files:**
- Create: `tests/substrate/test_git_ops.py`
- Create: `newmath_substrate/git_ops.py`

- [ ] **Step 1: 写失败测试 (用 temp_repo + 加 fake remote)**

```python
"""GitOps tests against real local git repos."""

import subprocess
from pathlib import Path
import pytest
from newmath_substrate.git_ops import GitOps


@pytest.fixture
def repo_with_remote(temp_repo: Path, tmp_path: Path) -> tuple[Path, Path]:
    """temp_repo + 一个 bare repo 作 origin remote.

    用法: (local_repo, bare_remote) = repo_with_remote
    """
    bare = tmp_path / "remote.git"
    subprocess.run(["git", "init", "--bare", str(bare)], check=True, capture_output=True)
    subprocess.run(
        ["git", "remote", "add", "origin", str(bare)],
        cwd=temp_repo, check=True,
    )
    subprocess.run(
        ["git", "push", "-u", "origin", "main"],
        cwd=temp_repo, check=True, capture_output=True,
    )
    return temp_repo, bare


def test_fetch_and_merge_basic(repo_with_remote: tuple[Path, Path]):
    """fetch + merge origin/main 干净的 case → ff."""
    local, bare = repo_with_remote
    # 模拟远端有新 commit: 第二个 worktree push 一个 commit
    # (简化: 直接在 local 改 + push)
    # 实际上这测试只验证 fetch + merge 不抛, 不验证更复杂逻辑

    git_ops = GitOps(wt_path=local)
    git_ops.fetch_and_merge(branch="main")  # 不抛 = pass
```

- [ ] **Step 2: 跑看失败**

```bash
pytest tests/substrate/test_git_ops.py::test_fetch_and_merge_basic -v
```

Expected: ImportError.

- [ ] **Step 3: 写实现 (基本 fetch+merge, 后续 task 加重试 / 冲突处理)**

```python
"""Git operations wrapper.

设计: 单一 class 装 fetch / merge / push / quiet-window / retry. codex review 中
T2 提到这是 monolith 风险, V1 接受为 monolith (≤220 LOC 硬指标), V2 看是否拆分.
"""

import subprocess
import time
from pathlib import Path
from newmath_substrate.exceptions import (
    GitOpsPushRejected, GitOpsMergeConflict, GitOpsError,
)


class GitOps:
    """每个 GitOps 绑定一个 worktree (在该 wt 内执行 git op)."""

    def __init__(self, wt_path: Path):
        self.wt_path = wt_path

    def fetch_and_merge(self, branch: str) -> None:
        """git fetch origin + git merge origin/<branch>.
        不用 rebase (CLAUDE.md 项目纪律).

        Raises:
            GitOpsMergeConflict: merge 有冲突
            GitOpsError: 其他 git 失败
        """
        # fetch
        r = subprocess.run(
            ["git", "fetch", "origin", branch],
            cwd=self.wt_path, capture_output=True, text=True,
        )
        if r.returncode != 0:
            raise GitOpsError(f"fetch failed: {r.stderr[:200]}")

        # merge (no rebase per CLAUDE.md)
        r = subprocess.run(
            ["git", "merge", f"origin/{branch}", "--no-edit"],
            cwd=self.wt_path, capture_output=True, text=True,
        )
        if r.returncode != 0:
            if "CONFLICT" in r.stdout or "CONFLICT" in r.stderr:
                # abort partial merge
                subprocess.run(
                    ["git", "merge", "--abort"],
                    cwd=self.wt_path, capture_output=True,
                )
                raise GitOpsMergeConflict(f"merge conflict on {branch}")
            raise GitOpsError(f"merge failed: {r.stderr[:200]}")
```

- [ ] **Step 4: 跑测试**

```bash
pytest tests/substrate/test_git_ops.py -v
```

Expected: 1 passed.

- [ ] **Step 5: Commit**

```bash
git add tests/substrate/test_git_ops.py newmath_substrate/git_ops.py
git commit -m "feat(substrate): GitOps.fetch_and_merge basic"
```

### Task 14: GitOps.merge_to_base_with_retry()

**Files:**
- Modify: `tests/substrate/test_git_ops.py`
- Modify: `newmath_substrate/git_ops.py`

- [ ] **Step 1: 加测试 (mock subprocess 模拟 push 一次失败一次成功)**

```python
def test_merge_to_base_with_retry_first_push_fails(repo_with_remote, monkeypatch):
    local, bare = repo_with_remote
    # 在 wt 里改一个文件
    (local / "new.txt").write_text("new\n")
    subprocess.run(["git", "add", "new.txt"], cwd=local, check=True)
    subprocess.run(["git", "commit", "-m", "add new"], cwd=local, check=True)

    git_ops = GitOps(wt_path=local)

    # 模拟 push 第一次失败 (non-fast-forward), 第二次 (fetch+merge 后) 成功
    real_run = subprocess.run
    call_count = {"push": 0}
    def fake_run(cmd, **kwargs):
        if cmd[:2] == ["git", "push"]:
            call_count["push"] += 1
            if call_count["push"] == 1:
                # 第一次失败
                class R:
                    returncode = 1
                    stdout = ""
                    stderr = "! [rejected] (non-fast-forward)"
                return R()
        return real_run(cmd, **kwargs)
    monkeypatch.setattr(subprocess, "run", fake_run)

    git_ops.merge_to_base_with_retry(base_branch="main", message="test merge")

    # 验证 push 被调了 ≥2 次 (重试)
    assert call_count["push"] >= 2
```

- [ ] **Step 2: 跑看失败**

```bash
pytest tests/substrate/test_git_ops.py::test_merge_to_base_with_retry_first_push_fails -v
```

Expected: AttributeError (method 不存在).

- [ ] **Step 3: 加实现**

在 `GitOps` class 内追加:

```python
    MAX_PUSH_RETRY = 3

    def merge_to_base_with_retry(self, base_branch: str, message: str) -> None:
        """从当前 worktree 的 branch merge 到 base_branch + push.
        push 失败 (non-fast-forward) → fetch + merge + 重试, 最多 MAX_PUSH_RETRY 次.
        """
        # 当前 worker branch 名 (HEAD 引用)
        r = subprocess.run(
            ["git", "rev-parse", "--abbrev-ref", "HEAD"],
            cwd=self.wt_path, capture_output=True, text=True, check=True,
        )
        worker_branch = r.stdout.strip()

        # checkout base + merge worker_branch (no-ff for visibility)
        # 注: 在 worktree 内不能 checkout base (会被另一个 worktree 锁), 所以策略是直接 push worker branch
        # 然后由 base branch checkout 一方 merge. V1 简化: push worker branch + merge via PR-like flow.
        # 这里实现是 push 当前 branch, base 一侧的 cutover supervisor 负责 merge.
        # (TODO Task 15: 加 PR-creation 或 base-branch-checkout 模式 — 此 task 不包含)

        for attempt in range(self.MAX_PUSH_RETRY):
            r = subprocess.run(
                ["git", "push", "origin", worker_branch],
                cwd=self.wt_path, capture_output=True, text=True,
            )
            if r.returncode == 0:
                return
            if "non-fast-forward" in r.stderr or "rejected" in r.stderr:
                # fetch + merge + retry
                self.fetch_and_merge(branch=worker_branch)
                continue
            raise GitOpsPushRejected(f"push failed: {r.stderr[:200]}")

        raise GitOpsPushRejected(
            f"push to {worker_branch} failed after {self.MAX_PUSH_RETRY} retries"
        )
```

- [ ] **Step 4: 跑测试**

```bash
pytest tests/substrate/test_git_ops.py -v
```

Expected: 2 passed.

- [ ] **Step 5: Commit**

```bash
git add tests/substrate/test_git_ops.py newmath_substrate/git_ops.py
git commit -m "feat(substrate): GitOps.merge_to_base_with_retry with push retry on non-fast-forward"
```

### Task 15: GitOps.quiet_window_check()

**Files:**
- Modify: `tests/substrate/test_git_ops.py`
- Modify: `newmath_substrate/git_ops.py`

- [ ] **Step 1: 加测试 (mock `gh run list` output)**

```python
def test_quiet_window_check_busy_returns_false(monkeypatch, repo_with_remote):
    local, _ = repo_with_remote
    # mock gh: 3 个 in_progress
    def fake_run(cmd, **kwargs):
        if cmd[:2] == ["gh", "run"]:
            class R:
                returncode = 0
                stdout = "in_progress\nin_progress\nin_progress\ncompleted\n"
                stderr = ""
            return R()
        return subprocess.run(cmd, **kwargs)
    monkeypatch.setattr(subprocess, "run", fake_run)

    git_ops = GitOps(wt_path=local)
    assert git_ops.quiet_window_check(branch="codex-auto-dev") is False


def test_quiet_window_check_quiet_returns_true(monkeypatch, repo_with_remote):
    local, _ = repo_with_remote
    def fake_run(cmd, **kwargs):
        if cmd[:2] == ["gh", "run"]:
            class R:
                returncode = 0
                stdout = "completed\ncompleted\n"  # 0 in_progress
                stderr = ""
            return R()
        return subprocess.run(cmd, **kwargs)
    monkeypatch.setattr(subprocess, "run", fake_run)

    git_ops = GitOps(wt_path=local)
    assert git_ops.quiet_window_check(branch="codex-auto-dev") is True
```

- [ ] **Step 2: 跑看失败**

```bash
pytest tests/substrate/test_git_ops.py -k quiet_window -v
```

Expected: AttributeError.

- [ ] **Step 3: 加实现**

```python
    QUIET_THRESHOLD = 1  # ≤1 个 in_progress = 安静

    def quiet_window_check(self, branch: str) -> bool:
        """检查 GitHub Actions 是否安静. CLAUDE.md 推荐 push 前调.

        Returns:
            True if ≤QUIET_THRESHOLD runs in_progress, 否则 False
        """
        r = subprocess.run(
            ["gh", "run", "list", "--branch", branch, "--limit", "10",
             "--json", "status", "-q", ".[].status"],
            cwd=self.wt_path, capture_output=True, text=True,
        )
        if r.returncode != 0:
            # gh 不可用 / 网络断 → 假设安静 (fail-open: 不阻塞 push)
            return True
        in_progress = sum(1 for line in r.stdout.splitlines() if line == "in_progress")
        return in_progress <= self.QUIET_THRESHOLD
```

- [ ] **Step 4: 跑测试**

```bash
pytest tests/substrate/test_git_ops.py -k quiet_window -v
```

Expected: 2 passed.

- [ ] **Step 5: Commit**

```bash
git add tests/substrate/test_git_ops.py newmath_substrate/git_ops.py
git commit -m "feat(substrate): GitOps.quiet_window_check via gh run list"
```

### Task 16: GitOps LOC sanity check

- [ ] **Step 1: 检查 LOC + 总 method count**

```bash
wc -l newmath_substrate/git_ops.py
grep -c "    def " newmath_substrate/git_ops.py
```

Expected: ≤ 220 LOC. Method count: ~3-4. 超 → 拆 helper 或者 split method.

---

### Task 17: Pipeline ABC + Context dataclass

**Files:**
- Create: `tests/substrate/test_pipeline.py`
- Create: `newmath_substrate/pipeline.py`

- [ ] **Step 1: 写失败测试 — Pipeline 抽象方法**

```python
"""Pipeline base + Context dataclass tests."""

from abc import ABC
from pathlib import Path
import pytest
import logging
from newmath_substrate.pipeline import Pipeline, Context
from newmath_substrate.worktree_mgr import WorktreeMgr


def test_pipeline_is_abstract():
    """Pipeline 不能直接实例化 (有 abstract method)."""
    with pytest.raises(TypeError, match="abstract"):
        Pipeline()


def test_pipeline_subclass_requires_discover_and_run(tmp_path: Path):
    """子类必须实现 discover_tasks + run_task."""
    class IncompletePipeline(Pipeline):
        name = "incomplete"
        # 没实现 discover_tasks / run_task

    with pytest.raises(TypeError, match="abstract"):
        IncompletePipeline()


def test_pipeline_full_subclass_works(tmp_path: Path):
    """完整子类可实例化 + 可调用."""
    discovered = []
    executed = []

    class GoodPipeline(Pipeline):
        name = "good"
        base_branch = "main"

        def discover_tasks(self):
            return [{"id": "t1"}, {"id": "t2"}]

        def run_task(self, task):
            executed.append(task["id"])

    p = GoodPipeline()
    p.set_context(Context(
        repo_root=tmp_path,
        worktree_mgr=WorktreeMgr(repo_root=tmp_path, worktree_root=tmp_path / "wt"),
        logger=logging.getLogger("test"),
        config={},
    ))
    tasks = p.discover_tasks()
    assert tasks == [{"id": "t1"}, {"id": "t2"}]
    for t in tasks:
        p.run_task(t)
    assert executed == ["t1", "t2"]
```

- [ ] **Step 2: 跑看失败**

```bash
pytest tests/substrate/test_pipeline.py -v
```

Expected: ImportError.

- [ ] **Step 3: 写实现**

```python
"""Pipeline ABC + Context dataclass.

Pipeline 是所有 pipeline 文件继承的 base class.
Context 是 runner 实例化 pipeline 时注入的环境 (worktree mgr, logger, etc.).
"""

from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any
import logging

from newmath_substrate.worktree_mgr import WorktreeMgr


@dataclass
class Context:
    """Pipeline 运行环境. runner 实例化 pipeline 时构造并注入."""
    repo_root: Path
    worktree_mgr: WorktreeMgr
    logger: logging.Logger
    config: dict[str, Any] = field(default_factory=dict)
    # pipeline-specific 上下文 (e.g., BEDC manifest) 通过 config 传, 不放固定字段


class Pipeline(ABC):
    """所有 pipeline 文件继承自这个."""

    # 子类必须覆盖
    name: str = ""
    base_branch: str = "main"
    concurrency: int = 1

    def __init__(self):
        self.ctx: Context | None = None

    def set_context(self, ctx: Context) -> None:
        """runner 实例化后注入 ctx. pipeline.run_task 内通过 self.ctx 访问."""
        self.ctx = ctx

    @abstractmethod
    def discover_tasks(self) -> list[dict]:
        """返回未完成的 task 列表. 每个 task 是 dict, 内容由 pipeline 定义."""

    @abstractmethod
    def run_task(self, task: dict) -> None:
        """执行单 task. 抛异常 = 失败, runner log + skip + 下轮重试."""
```

- [ ] **Step 4: 跑测试**

```bash
pytest tests/substrate/test_pipeline.py -v
```

Expected: 3 passed.

- [ ] **Step 5: Commit**

```bash
git add tests/substrate/test_pipeline.py newmath_substrate/pipeline.py
git commit -m "feat(substrate): Pipeline ABC + Context dataclass"
```

### Task 18: newmath_substrate/__init__.py exports

**Files:**
- Modify: `newmath_substrate/__init__.py`

- [ ] **Step 1: 写 public API export**

```python
"""newmath_substrate: codex-on-worktree-with-gates pipeline framework foundation.

Public API:
    - Pipeline, Context: base class + injected env
    - WorktreeMgr: git worktree lifecycle
    - CodexCLI, CodexResult: codex exec wrapper
    - GateRunner, Gate, GateResult: gate composition
    - GitOps: git operations
    - 异常: SubstrateError 及子类
"""

from newmath_substrate.pipeline import Pipeline, Context
from newmath_substrate.worktree_mgr import WorktreeMgr
from newmath_substrate.codex_cli import CodexCLI, CodexResult
from newmath_substrate.gate_runner import GateRunner, Gate, GateResult
from newmath_substrate.git_ops import GitOps
from newmath_substrate.exceptions import (
    SubstrateError,
    WorktreeError, WorktreeNameClash, WorktreeCleanupFailed,
    CodexError, CodexAuth, CodexTimeout, CodexEmpty, CodexUnknown,
    GateFailed, GateTimeout,
    GitOpsError, GitOpsPushRejected, GitOpsMergeConflict,
)

__all__ = [
    "Pipeline", "Context",
    "WorktreeMgr",
    "CodexCLI", "CodexResult",
    "GateRunner", "Gate", "GateResult",
    "GitOps",
    "SubstrateError",
    "WorktreeError", "WorktreeNameClash", "WorktreeCleanupFailed",
    "CodexError", "CodexAuth", "CodexTimeout", "CodexEmpty", "CodexUnknown",
    "GateFailed", "GateTimeout",
    "GitOpsError", "GitOpsPushRejected", "GitOpsMergeConflict",
]
```

- [ ] **Step 2: 验证 import 不报错**

```bash
python3 -c "import newmath_substrate; print(newmath_substrate.__all__)"
```

Expected: 打印 list of exported names, 无 ImportError.

- [ ] **Step 3: Commit**

```bash
git add newmath_substrate/__init__.py
git commit -m "feat(substrate): export public API in __init__"
```

### Task 19: V1 substrate LOC + method-count baseline

**Files:**
- Modify: `docs/substrate_api.md`

- [ ] **Step 1: 计数实际 LOC + method**

```bash
wc -l newmath_substrate/*.py
grep -c "    def " newmath_substrate/*.py | grep -v __init__
```

记录每个文件 LOC + public method 数 (`def name` 不带 `_` 前缀).

- [ ] **Step 2: 把实际 baseline 写到 substrate_api.md 末尾**

更新 `docs/substrate_api.md`:

```markdown
## Spike-Locked Baseline (Phase 2 完成时记录, 不再变)

- Total LOC: <实际数字>
- Total public methods: <实际数字>
- Component count: 5 (Pipeline+Context = 1, + 4 个 substrate)
- Date locked: <实际日期>

API churn budget anchor: 后续 Phase (codex_formalize / codex_revise 迁移) 内, 总 method 数 OR 总 LOC 增量 >30% 触发 V2 review checkpoint.
```

- [ ] **Step 3: Commit baseline**

```bash
git add docs/substrate_api.md
git commit -m "docs(substrate): lock V1 LOC + method baseline for API churn budget"
```

---

## Phase 3: bedc_gates package

### Task 20: bedc_gates scaffolding

**Files:**
- Create: `bedc_gates/__init__.py`
- Create: `bedc_gates/base.py`

- [ ] **Step 1: 写 base 模块 (re-export GateResult, BEDC-specific gate 复用)**

`bedc_gates/base.py`:

```python
"""bedc_gates base: re-export substrate types + BEDC-common helpers.

设计原则: bedc_gates 是 BEDC-specific gate 实现, 跟 substrate 同级独立 package.
不会反向依赖 pipeline; 但可以用 substrate 的 GateResult 协议.
"""

from newmath_substrate.gate_runner import GateResult


__all__ = ["GateResult"]
```

`bedc_gates/__init__.py`:

```python
"""bedc_gates: BEDC-specific gate 实现 for substrate GateRunner."""

from bedc_gates.lake_build import LakeBuild
from bedc_gates.axiom_purity import AxiomPurity
from bedc_gates.bedc_ci_audit import BedcCiAudit
from bedc_gates.check_math_env import CheckMathEnv
from bedc_gates.check_tex_size import CheckTexSize

__all__ = [
    "LakeBuild", "AxiomPurity", "BedcCiAudit",
    "CheckMathEnv", "CheckTexSize",
]
```

- [ ] **Step 2: Commit**

```bash
git add bedc_gates/__init__.py bedc_gates/base.py
git commit -m "feat(bedc_gates): scaffold package"
```

(注: __init__.py 列出 5 个 import, 但实际文件 Task 21-25 才创建. 临时 import 会失败 — 不要急, 后面 task 会让它通过.)

### Task 21: LakeBuild gate

**Files:**
- Create: `tests/bedc_gates/test_lake_build.py`
- Create: `bedc_gates/lake_build.py`

- [ ] **Step 1: 失败测试 — mock subprocess**

```python
"""LakeBuild gate test."""

import subprocess
from pathlib import Path
import pytest
from bedc_gates.lake_build import LakeBuild


def test_lake_build_pass(monkeypatch, tmp_path: Path):
    """lake build exit 0 → GateResult passed=True."""
    def fake_run(cmd, **kwargs):
        class R:
            returncode = 0
            stdout = "Build complete\n"
            stderr = ""
        return R()
    monkeypatch.setattr(subprocess, "run", fake_run)

    gate = LakeBuild()
    result = gate(tmp_path)

    assert result.name == "lake-build"
    assert result.passed is True


def test_lake_build_fail(monkeypatch, tmp_path: Path):
    """lake build exit ≠0 → passed=False."""
    def fake_run(cmd, **kwargs):
        class R:
            returncode = 1
            stdout = ""
            stderr = "error: unknown identifier\n"
        return R()
    monkeypatch.setattr(subprocess, "run", fake_run)

    gate = LakeBuild()
    result = gate(tmp_path)
    assert result.passed is False
    assert "unknown identifier" in result.stderr
```

- [ ] **Step 2: 跑看失败**

```bash
pytest tests/bedc_gates/test_lake_build.py -v
```

Expected: ImportError.

- [ ] **Step 3: 写实现**

`bedc_gates/lake_build.py`:

```python
"""LakeBuild gate: 跑 `lake build` 在 worktree/lean4/ 内."""

import subprocess
from pathlib import Path
from bedc_gates.base import GateResult


class LakeBuild:
    """Gate: 跑 `cd lean4 && lake build`. exit 0 = pass."""
    name = "lake-build"

    def __init__(self, lean4_subdir: str = "lean4", timeout: int = 1800):
        self.lean4_subdir = lean4_subdir
        self.timeout = timeout

    def __call__(self, wt: Path) -> GateResult:
        lean4_dir = wt / self.lean4_subdir
        try:
            result = subprocess.run(
                ["lake", "build"],
                cwd=lean4_dir, capture_output=True, text=True, timeout=self.timeout,
            )
        except subprocess.TimeoutExpired:
            return GateResult(name=self.name, exit_code=124, stderr=f"timeout after {self.timeout}s")
        return GateResult(
            name=self.name,
            exit_code=result.returncode,
            stderr=result.stderr,
        )
```

- [ ] **Step 4: 跑测试**

```bash
pytest tests/bedc_gates/test_lake_build.py -v
```

Expected: 2 passed.

- [ ] **Step 5: Commit**

```bash
git add tests/bedc_gates/test_lake_build.py bedc_gates/lake_build.py
git commit -m "feat(bedc_gates): LakeBuild gate"
```

### Task 22: AxiomPurity gate

**Files:**
- Create: `tests/bedc_gates/test_axiom_purity.py`
- Create: `bedc_gates/axiom_purity.py`

- [ ] **Step 1-4 same pattern as Task 21**

测试 mock subprocess. 实现:

```python
"""AxiomPurity gate: 跑 `python3 lean4/scripts/bedc_ci.py axiom-purity --strict`."""

import subprocess
from pathlib import Path
from bedc_gates.base import GateResult


class AxiomPurity:
    name = "axiom-purity"

    def __init__(self, script: str = "lean4/scripts/bedc_ci.py", timeout: int = 600):
        self.script = script
        self.timeout = timeout

    def __call__(self, wt: Path) -> GateResult:
        try:
            result = subprocess.run(
                ["python3", self.script, "axiom-purity", "--strict"],
                cwd=wt, capture_output=True, text=True, timeout=self.timeout,
            )
        except subprocess.TimeoutExpired:
            return GateResult(name=self.name, exit_code=124, stderr=f"timeout after {self.timeout}s")
        return GateResult(name=self.name, exit_code=result.returncode, stderr=result.stderr)
```

测试同 Task 21 pattern, 调整 cmd assertion.

- [ ] **Step 5: Commit**

```bash
git commit -m "feat(bedc_gates): AxiomPurity gate"
```

### Task 23: BedcCiAudit gate

**Files:**
- Create: `tests/bedc_gates/test_bedc_ci_audit.py`
- Create: `bedc_gates/bedc_ci_audit.py`

同 pattern. 命令是 `python3 lean4/scripts/bedc_ci.py audit`.

```python
class BedcCiAudit:
    name = "bedc-ci-audit"

    def __init__(self, script: str = "lean4/scripts/bedc_ci.py", timeout: int = 300):
        self.script = script
        self.timeout = timeout

    def __call__(self, wt: Path) -> GateResult:
        try:
            result = subprocess.run(
                ["python3", self.script, "audit"],
                cwd=wt, capture_output=True, text=True, timeout=self.timeout,
            )
        except subprocess.TimeoutExpired:
            return GateResult(name=self.name, exit_code=124, stderr=f"timeout after {self.timeout}s")
        return GateResult(name=self.name, exit_code=result.returncode, stderr=result.stderr)
```

```bash
git commit -m "feat(bedc_gates): BedcCiAudit gate"
```

### Task 24: CheckMathEnv + CheckTexSize gates

同 pattern, 命令分别是 `papers/bedc/scripts/check_math_env.sh` 和 `papers/bedc/scripts/check_tex_size.sh`.

```python
class CheckMathEnv:
    name = "check-math-env"

    def __init__(self, script: str = "papers/bedc/scripts/check_math_env.sh", timeout: int = 60):
        self.script = script
        self.timeout = timeout

    def __call__(self, wt: Path) -> GateResult:
        try:
            result = subprocess.run(
                ["bash", self.script],
                cwd=wt, capture_output=True, text=True, timeout=self.timeout,
            )
        except subprocess.TimeoutExpired:
            return GateResult(name=self.name, exit_code=124, stderr=f"timeout after {self.timeout}s")
        return GateResult(name=self.name, exit_code=result.returncode, stderr=result.stderr)
```

(CheckTexSize 同, 改 script 路径)

- [ ] **Steps**: 测试 + 实现 + commit. Each gate 一个 commit.

```bash
git commit -m "feat(bedc_gates): CheckMathEnv + CheckTexSize gates"
```

### Task 25: bedc_gates __init__.py 现在 import 全部能跑

- [ ] **Step 1: 验证 import 不报错**

```bash
python3 -c "import bedc_gates; print(bedc_gates.__all__)"
```

Expected: 5 个 gate 名字打印, 无 ImportError.

- [ ] **Step 2: 跑所有 bedc_gates 测试**

```bash
pytest tests/bedc_gates/ -v
```

Expected: 10 passed (每个 gate 2 test × 5 gate).

---

## Phase 4: sync pipeline validation

### Task 26: 读 sync_with_auto_dev.py + 抽业务逻辑

**Files:**
- Read: `tools/sync_with_auto_dev.py`
- Create: `docs/superpowers/spike-notes/sync_pipeline_plan.md`

- [ ] **Step 1: 通读 + 列出业务逻辑步骤 (非 substrate 部分)**

记录 `tools/sync_with_auto_dev.py` 实际做的事:
1. 从哪里 fetch
2. merge 到哪里
3. 触发条件 (定时? 事件? 命令)
4. commit message 格式
5. 失败时怎么处理

写到 `docs/superpowers/spike-notes/sync_pipeline_plan.md`:

```markdown
# sync pipeline business logic

## 现状 (tools/sync_with_auto_dev.py)
- 触发: <cron / 手动 / supervisor 调用>
- 主要动作: <list step by step>
- commit message 格式: <格式>
- 失败处理: <retry / log / abort>

## 用 substrate 重写后的 pipeline 形状
- discover_tasks 返回什么: <e.g., 单 task "sync from auto-dev">
- run_task 做什么: <step 1, step 2, ...>
- 哪些 substrate API 调用: GitOps.fetch_and_merge, GitOps.safe_push, ...
- 不调 CodexCLI / GateRunner (sync 是辅助 pipeline, 不跑 codex / gate)
```

- [ ] **Step 2: Commit notes**

```bash
git add docs/superpowers/spike-notes/sync_pipeline_plan.md
git commit -m "spike: sync pipeline business logic inventory"
```

### Task 27: sync pipeline file

**Files:**
- Create: `pipelines/sync.py`
- Create: `tests/pipelines/test_sync.py`

- [ ] **Step 1: 写失败测试 — pipeline 实例化 + discover + run (mock substrate)**

```python
"""sync pipeline smoke test (mocks substrate at unit level)."""

from pathlib import Path
import logging
import pytest
from unittest.mock import MagicMock, patch
from pipelines.sync import SyncPipeline
from newmath_substrate import Context, WorktreeMgr


def test_sync_pipeline_discover_returns_single_task(tmp_path: Path):
    """Sync 是辅助 pipeline, discover_tasks 返回一个 sync task."""
    pipeline = SyncPipeline()
    pipeline.set_context(Context(
        repo_root=tmp_path,
        worktree_mgr=MagicMock(spec=WorktreeMgr),
        logger=logging.getLogger("test"),
        config={},
    ))

    tasks = pipeline.discover_tasks()
    assert len(tasks) == 1
    assert tasks[0]["kind"] == "sync"


def test_sync_pipeline_run_task_calls_git_ops(tmp_path: Path):
    """run_task 应调用 GitOps.fetch_and_merge."""
    mock_wt_mgr = MagicMock(spec=WorktreeMgr)
    mock_wt_mgr.create.return_value = tmp_path / "wt"
    (tmp_path / "wt").mkdir()

    pipeline = SyncPipeline()
    pipeline.set_context(Context(
        repo_root=tmp_path,
        worktree_mgr=mock_wt_mgr,
        logger=logging.getLogger("test"),
        config={"source_branch": "auto-dev", "target_branch": "dev"},
    ))

    with patch("pipelines.sync.GitOps") as mock_git_ops_cls:
        mock_git_ops = mock_git_ops_cls.return_value
        pipeline.run_task({"kind": "sync", "id": "sync-1"})

        mock_git_ops.fetch_and_merge.assert_called_once()
```

- [ ] **Step 2: 跑看失败**

```bash
pytest tests/pipelines/test_sync.py -v
```

Expected: ImportError.

- [ ] **Step 3: 写实现**

```python
"""Sync pipeline: 替代 tools/sync_with_auto_dev.py.

辅助 pipeline (不跑 codex / gate), 只做 git 同步.
"""

from newmath_substrate import Pipeline, GitOps


class SyncPipeline(Pipeline):
    name = "sync"
    base_branch = "dev"
    concurrency = 1  # sync 不并发 (会冲突)

    def discover_tasks(self) -> list[dict]:
        """sync 不读外部 queue, 每次 supervisor 唤醒就执行一次同步."""
        return [{"kind": "sync", "id": f"sync-{self.ctx.config.get('cycle', 0)}"}]

    def run_task(self, task: dict) -> None:
        """从 source_branch fetch + merge 到 target_branch."""
        source = self.ctx.config["source_branch"]
        target = self.ctx.config["target_branch"]

        wt = self.ctx.worktree_mgr.create(
            branch_name=f"sync-{task['id']}",
            base_branch=target,
        )
        try:
            git_ops = GitOps(wt_path=wt)
            git_ops.fetch_and_merge(branch=source)
            git_ops.merge_to_base_with_retry(
                base_branch=target,
                message=f"sync: merge {source} into {target} ({task['id']})",
            )
            self.ctx.logger.info(f"sync completed: {source} → {target}")
        finally:
            self.ctx.worktree_mgr.cleanup(wt)
```

- [ ] **Step 4: 跑测试**

```bash
pytest tests/pipelines/test_sync.py -v
```

Expected: 2 passed.

- [ ] **Step 5: LOC check**

```bash
wc -l pipelines/sync.py
```

Expected: ≤ 150 LOC (辅助型 pipeline 目标).

- [ ] **Step 6: Commit**

```bash
git add tests/pipelines/test_sync.py pipelines/sync.py
git commit -m "feat(pipelines): sync pipeline replaces tools/sync_with_auto_dev.py"
```

### Task 28: substrate contract test 文件

**Files:**
- Create: `scripts/substrate_contract_test.py`

- [ ] **Step 1: 写 contract test 文件 (跨 component golden tests)**

```python
"""Substrate contract tests: golden behavior tests, ≥3 per V1 component.

跑法: pytest scripts/substrate_contract_test.py -v
后续 substrate 改动必须保这些 test 绿. 这是 API churn budget 的具体守门员.
"""

import subprocess
from pathlib import Path
import logging
import pytest
from unittest.mock import MagicMock

from newmath_substrate import (
    Pipeline, Context, WorktreeMgr, CodexCLI, GateRunner, GateResult, GitOps,
)
from newmath_substrate.exceptions import WorktreeNameClash, CodexAuth, GateFailed


# === WorktreeMgr golden tests ===

class TestWorktreeMgrGolden:
    def test_create_returns_path(self, temp_repo: Path, temp_worktree_root: Path):
        mgr = WorktreeMgr(repo_root=temp_repo, worktree_root=temp_worktree_root)
        wt = mgr.create("feat/x", "dev")
        assert wt.exists()

    def test_create_clash_raises(self, temp_repo: Path, temp_worktree_root: Path):
        mgr = WorktreeMgr(repo_root=temp_repo, worktree_root=temp_worktree_root)
        mgr.create("feat/x", "dev")
        with pytest.raises(WorktreeNameClash):
            mgr.create("feat/x", "dev")

    def test_dirty_restart_skip_detects_lock(self, temp_repo: Path, temp_worktree_root: Path):
        mgr = WorktreeMgr(repo_root=temp_repo, worktree_root=temp_worktree_root)
        wt = mgr.create("feat/dirty", "dev")
        (wt / ".runner-lock").write_text("pid")
        assert mgr.dirty_restart_skip(wt) is True


# === CodexCLI golden tests ===

class TestCodexCLIGolden:
    def test_exec_happy_returns_result(self, monkeypatch, tmp_path: Path):
        class FakeR:
            returncode = 0
            stdout = "ok\n"
            stderr = ""
        monkeypatch.setattr(subprocess, "run", lambda c, **k: FakeR())
        cli = CodexCLI(tmp_path)
        r = cli.exec("p")
        assert r.exit_code == 0

    def test_exec_auth_failure(self, monkeypatch, tmp_path: Path):
        class FakeR:
            returncode = 1
            stdout = ""
            stderr = "unauthorized"
        monkeypatch.setattr(subprocess, "run", lambda c, **k: FakeR())
        cli = CodexCLI(tmp_path)
        with pytest.raises(CodexAuth):
            cli.exec("p")

    def test_exec_timeout_classified(self, monkeypatch, tmp_path: Path):
        def fake(cmd, **k):
            raise subprocess.TimeoutExpired(cmd, timeout=1)
        monkeypatch.setattr(subprocess, "run", fake)
        cli = CodexCLI(tmp_path)
        from newmath_substrate.exceptions import CodexTimeout
        with pytest.raises(CodexTimeout):
            cli.exec("p", timeout=1)


# === GateRunner golden tests ===

class TestGateRunnerGolden:
    def test_all_pass(self, tmp_path: Path):
        gates = [lambda wt: GateResult("g1", 0), lambda wt: GateResult("g2", 0)]
        # 用 callable, 给每个 callable 加 name attr
        gates[0].name = "g1"
        gates[1].name = "g2"
        runner = GateRunner(gates)
        runner.require_pass(tmp_path)  # 不抛

    def test_first_fail_short_circuit(self, tmp_path: Path):
        called_second = []
        g1 = lambda wt: GateResult("g1", 1, "boom")
        g1.name = "g1"
        def g2_impl(wt):
            called_second.append(True)
            return GateResult("g2", 0)
        g2_impl.name = "g2"
        runner = GateRunner([g1, g2_impl])
        with pytest.raises(GateFailed):
            runner.require_pass(tmp_path)
        assert called_second == []

    def test_gate_result_passed_property(self):
        assert GateResult("x", 0).passed is True
        assert GateResult("x", 1).passed is False


# === GitOps golden tests ===

class TestGitOpsGolden:
    def test_fetch_and_merge_no_remote_raises(self, tmp_path: Path):
        from newmath_substrate.exceptions import GitOpsError
        # 没 remote 的 repo
        subprocess.run(["git", "init", "-q"], cwd=tmp_path, check=True)
        ops = GitOps(wt_path=tmp_path)
        with pytest.raises(GitOpsError):
            ops.fetch_and_merge(branch="main")

    def test_quiet_window_gh_unavailable_returns_true(self, monkeypatch, tmp_path: Path):
        """gh 不可用时 fail-open."""
        def fake(cmd, **k):
            class R:
                returncode = 1
                stdout = ""
                stderr = "gh: command not found"
            return R()
        monkeypatch.setattr(subprocess, "run", fake)
        ops = GitOps(wt_path=tmp_path)
        assert ops.quiet_window_check(branch="main") is True

    def test_merge_retry_count_capped(self):
        """MAX_PUSH_RETRY constant 存在."""
        assert hasattr(GitOps, "MAX_PUSH_RETRY")
        assert GitOps.MAX_PUSH_RETRY >= 1


# === Pipeline + Context golden tests ===

class TestPipelineGolden:
    def test_pipeline_abstract_cannot_instantiate(self):
        with pytest.raises(TypeError):
            Pipeline()

    def test_context_dataclass_fields(self, tmp_path: Path):
        mgr = MagicMock(spec=WorktreeMgr)
        ctx = Context(
            repo_root=tmp_path,
            worktree_mgr=mgr,
            logger=logging.getLogger("test"),
            config={"k": "v"},
        )
        assert ctx.repo_root == tmp_path
        assert ctx.config["k"] == "v"

    def test_subclass_with_run_works(self, tmp_path: Path):
        class P(Pipeline):
            name = "p"
            def discover_tasks(self): return [{"id": "1"}]
            def run_task(self, t): pass
        p = P()
        ctx = Context(
            repo_root=tmp_path,
            worktree_mgr=MagicMock(spec=WorktreeMgr),
            logger=logging.getLogger("t"),
            config={},
        )
        p.set_context(ctx)
        assert p.discover_tasks() == [{"id": "1"}]
```

- [ ] **Step 2: 跑 contract test**

```bash
pytest scripts/substrate_contract_test.py -v
```

Expected: 15 passed (5 component × 3 golden).

- [ ] **Step 3: Commit**

```bash
git add scripts/substrate_contract_test.py
git commit -m "test(substrate): contract tests, 15 golden across 5 components"
```

### Task 29: End-to-end smoke — sync pipeline 跑通

**Files:**
- (no new file, 命令测试)

- [ ] **Step 1: 跑全 test suite**

```bash
pytest tests/ scripts/substrate_contract_test.py -v
```

Expected: 所有 test pass. 加总: ~25-30 个 test. 失败任何一个都要回去修.

- [ ] **Step 2: 手动 smoke test sync pipeline (在 feat-pipeline-runner 分支上)**

写一个临时 runner stub 跑 sync 一次:

```bash
cat > /tmp/run_sync_once.py << 'EOF'
"""一次性跑 sync pipeline, 验证 happy path."""
import sys, logging
from pathlib import Path
sys.path.insert(0, "/Users/auric/newmath")
from newmath_substrate import Context, WorktreeMgr
from pipelines.sync import SyncPipeline

logging.basicConfig(level=logging.INFO)

ctx = Context(
    repo_root=Path("/Users/auric/newmath"),
    worktree_mgr=WorktreeMgr(
        repo_root=Path("/Users/auric/newmath"),
        worktree_root=Path("/tmp/newmath-wt"),
    ),
    logger=logging.getLogger("sync"),
    config={
        "source_branch": "auto-dev",
        "target_branch": "feat-pipeline-runner",  # 跟自己同步, 安全
        "cycle": 0,
    },
)
p = SyncPipeline()
p.set_context(ctx)
for task in p.discover_tasks():
    p.run_task(task)
print("DONE")
EOF
python3 /tmp/run_sync_once.py
```

Expected: 打印 `sync completed: auto-dev → feat-pipeline-runner` + `DONE`. 没 traceback.

- [ ] **Step 3: 验证 git 状态没坏**

```bash
git status
git log --oneline -5
```

Expected: branch 上有一个 merge commit 或者 ff-merge. 不 broken.

- [ ] **Step 4: 清掉 worktree**

```bash
rm -rf /tmp/newmath-wt /tmp/run_sync_once.py
git worktree prune
```

- [ ] **Step 5: Commit smoke test note**

```bash
# 加一个 docs 记录 smoke test 结果
cat > docs/superpowers/spike-notes/v1-foundation-smoke-test.md << 'EOF'
# V1 Foundation Smoke Test

Date: <填日期>
Branch: feat-pipeline-runner

Result: PASS
- All pytest tests green (~30 tests)
- Contract tests green (15 golden)
- Manual sync pipeline run: completed without error
- git status clean after smoke test
EOF
git add docs/superpowers/spike-notes/v1-foundation-smoke-test.md
git commit -m "test(v1-foundation): smoke test sync pipeline end-to-end"
```

---

## Phase 5: PR + 文档

### Task 30: Update CLAUDE.md for new structure

**Files:**
- Modify: `CLAUDE.md`

- [ ] **Step 1: 加新 section 描述 substrate + pipeline 结构**

在 CLAUDE.md 的 "项目结构" 节追加 (不要删现有内容):

```markdown
## V1 Pipeline Framework

- `newmath_substrate/` — codex-on-worktree-with-gates 复用 library (BEDC-agnostic, 5 component)
- `bedc_gates/` — BEDC-specific gate (LakeBuild / AxiomPurity / BedcCiAudit / ...)
- `pipelines/` — 各 pipeline 文件, import substrate. 加新 pipeline = drop a file + restart runner
- `scripts/substrate_contract_test.py` — substrate API churn budget 守门员
- `docs/substrate_api.md` — substrate API spec (V1 spike-locked baseline)

注: V1 不含 runner daemon. 跑 pipeline 用 `python -m pipelines.<name>` 直接调.
后续 Phase 5 实现 newmath_runner.py 后改为 daemon 模式.
```

- [ ] **Step 2: Commit**

```bash
git add CLAUDE.md
git commit -m "docs: CLAUDE.md V1 pipeline framework structure"
```

### Task 31: 创建 PR

- [ ] **Step 1: Push branch**

```bash
git push -u origin feat-pipeline-runner
```

- [ ] **Step 2: 创建 PR**

```bash
gh pr create --base dev --title "feat: V1 pipeline framework foundation (substrate + bedc_gates + sync)" --body "$(cat <<'EOF'
## Summary

V1 Foundation 阶段产出, 实施 design doc `~/.gstack/projects/the-omega-institute-newmath/auric-auto-dev-design-20260511-210724.md` 的 Phase 1-4.

- `newmath_substrate/` — 5 component (Pipeline+Context / WorktreeMgr / CodexCLI / GateRunner / GitOps), V1 ≤1000 LOC
- `bedc_gates/` — 5 gate (LakeBuild / AxiomPurity / BedcCiAudit / CheckMathEnv / CheckTexSize)
- `pipelines/sync.py` — 第一个 production pipeline, 替代 `tools/sync_with_auto_dev.py` (后者本 PR 暂不删, 等 Phase 5 runner 上线后再删)
- 15 contract tests + ~20 unit tests, 全绿
- API baseline locked in `docs/substrate_api.md`

## NOT in this PR (后续 phase)

- codex_formalize / codex_revise 迁移 (Phase 5/6)
- newmath_runner.py daemon (Phase 5)
- 旧脚本下线 (Phase 5 cutover)

## Test plan

- [ ] pytest tests/ scripts/substrate_contract_test.py - all green
- [ ] python3 -m pipelines.sync 一次 smoke test 不报错
- [ ] git worktree list 显示没残留 worktree
- [ ] API churn check: substrate_api.md 列出的 method 数 / LOC 都没超 baseline +30%

🤖 Generated with [Claude Code](https://claude.com/claude-code)
EOF
)"
```

- [ ] **Step 2: 获取 PR URL 给用户**

`gh pr create` 输出 PR URL, 反馈给用户.

---

## Self-Review Checklist (after writing this plan)

- [x] 每个 task 步骤 2-5 分钟可完成
- [x] 每个 step 含真实 code / command, 不是 "implement appropriately"
- [x] file paths 准确
- [x] commit 频率: 每个 task 末尾 commit
- [x] TDD pattern: 写测试 → 看失败 → 写实现 → 看通过 → commit
- [x] DRY: bedc_gates 5 个 gate 都是同 pattern, 但每个有自己的命令/路径, 不是 copy-paste
- [x] YAGNI: 不实现 V2 component (PromptLoader / TaskQueue / NamedLock / Logger), 等 V1 跑通 3 pipeline 才决定
- [x] 函数命名一致: WorktreeMgr.create / cleanup / dirty_restart_skip / list_dirty 全 plan 一致
- [x] LOC budget check: 每个 component 有 sanity check task

## Known Limitations / Spike-time Decisions

设计 review 留的 unresolved (实施时观察 + 决定):

1. **Pipeline base + Context 归属**: 默认 substrate (5th component). Spike 后如发现 ctx 跟 runner 耦合更紧 (e.g., ctx 需要 runner 的 concurrency cap 状态), 可下沉 runner.py, import 调整即可.

2. **GitOps 拆分**: Codex review 中 T2 提到 fetch+merge+push 是不同 failure domain. V1 接受 monolith (≤220 LOC 硬指标), V2 看是否拆 `GitFetch` + `GitMerge` + `GitPush`.

3. **GateRunner per-gate timeout**: V1 没在 GateRunner 加 timeout, 每个 gate 自己在 subprocess.run 里 timeout. V2 考虑加 framework-level wrapper timeout (防 gate 死循环 hang).

4. **Observability**: V1 用 stdlib logging. 跑通 3 pipeline 后 retro 是否要 structured event log (e.g., per-task lifecycle events).

5. **bedc_gates 跟 substrate 的耦合度**: V1 接受 bedc_gates 完全独立 (只 import substrate 的 GateResult). 如果未来发现 BEDC-specific gate 需要更多 substrate 上下文, 可放 substrate 的 `ProtocolGate` 协议引入.

---

## Estimated Total

- Phase 1 (spike): ~1 周
- Phase 2 (substrate impl): ~2 周
- Phase 3 (bedc_gates): ~0.5 周
- Phase 4 (sync pipeline): ~0.5 周
- Phase 5 (PR + docs): ~2 天

Total: ~4 周 一个 senior dev / CC + gstack ~1-2 天 跑完所有 task (subagent driven).

后续 plans (单独写):
- **Plan B**: 迁移 `lean4/scripts/codex_formalize.py` → `pipelines/codex_formalize.py` (2-3 周, V1 substrate stress test #2)
- **Plan C**: 迁移 `papers/bedc/scripts/codex_revise.py` → `pipelines/codex_revise.py` (1-2 周)
- **Plan D**: `newmath_runner.py` daemon + cutover + 旧脚本下线 (1 周)
