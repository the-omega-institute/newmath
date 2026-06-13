from __future__ import annotations

import importlib.util
import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
POLICY_PATH = REPO_ROOT / "tools" / "bedc_quality_canonical_generated_merge.py"
CANONICAL_PREFIX = "papers/bedc-quality-lab/reports/canonical/"


def _load_policy_module():
    spec = importlib.util.spec_from_file_location("canonical_generated_merge_policy", POLICY_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load canonical generated merge policy")
    module = importlib.util.module_from_spec(spec)
    old_module = sys.modules.pop(spec.name, None)
    try:
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)
        return module
    finally:
        if old_module is not None:
            sys.modules[spec.name] = old_module
        else:
            sys.modules.pop(spec.name, None)


policy_module = _load_policy_module()


def _git(
    repo: Path,
    *args: str,
    check: bool = True,
    input_text: str | None = None,
) -> subprocess.CompletedProcess[str]:
    res = subprocess.run(
        ["git", *args],
        cwd=repo,
        text=True,
        capture_output=True,
        input=input_text,
    )
    if check and res.returncode != 0:
        raise AssertionError(
            f"git {' '.join(args)} failed with {res.returncode}\n"
            f"stdout:\n{res.stdout}\nstderr:\n{res.stderr}"
        )
    return res


def _write(repo: Path, rel: str, text: str) -> None:
    path = repo / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _read(repo: Path, rel: str) -> str:
    return (repo / rel).read_text(encoding="utf-8")


def _commit(repo: Path, message: str) -> None:
    _git(repo, "add", "-A")
    _git(repo, "commit", "-m", message)


def _init_repo(tmp_path: Path) -> Path:
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q", "-b", "main")
    _git(repo, "config", "user.email", "tester@example.invalid")
    _git(repo, "config", "user.name", "Test User")
    _write(
        repo,
        ".gitattributes",
        "\n".join(
            [
                "papers/bedc-quality-lab/reports/canonical/** "
                "merge=bedc-quality-canonical-generated",
                "",
            ]
        ),
    )
    _commit(repo, "base")
    return repo


def _install_driver(repo: Path) -> None:
    policy_module.CanonicalGeneratedMergePolicy(repo).install_driver()


def _unmerged_paths(repo: Path) -> list[str]:
    return _git(repo, "diff", "--name-only", "--diff-filter=U").stdout.splitlines()


def _merge(repo: Path, branch: str) -> subprocess.CompletedProcess[str]:
    return _git(repo, "merge", "--no-ff", "--no-edit", branch, check=False)


def _checkout_branch(repo: Path, branch: str, start: str = "main") -> None:
    _git(repo, "checkout", "-q", "-B", branch, start)


def test_install_driver_check_and_attribute_scope(tmp_path: Path) -> None:
    repo = _init_repo(tmp_path)
    policy = policy_module.CanonicalGeneratedMergePolicy(repo)

    check_before = subprocess.run(
        [
            sys.executable,
            str(POLICY_PATH),
            "install-driver",
            "--repo",
            str(repo),
            "--check",
        ],
        text=True,
        capture_output=True,
    )
    assert check_before.returncode == 2
    assert "driver config drift" in check_before.stderr

    policy.install_driver()
    policy.install_driver(check=True)

    attr = _git(
        repo,
        "check-attr",
        "merge",
        "--",
        f"{CANONICAL_PREFIX}index.json",
        "papers/bedc-quality-lab/bedc_quality_lab/source_probe.py",
        "papers/bedc-quality-lab/scripts/run_canonical_reports.py",
        "papers/bedc-quality-lab/tests/test_canonical_reports.py",
        "papers/bedc-quality-lab/docs/source_probe.md",
        "papers/bedc-quality-lab/configs/source_probe.json",
        "papers/bedc-quality-lab/reports/runs/run_probe.json",
        "papers/bedc-quality-lab/reports/source_probe.json",
    ).stdout
    assert f"{CANONICAL_PREFIX}index.json: merge: bedc-quality-canonical-generated" in attr
    assert "bedc_quality_lab/source_probe.py: merge: unspecified" in attr
    assert "scripts/run_canonical_reports.py: merge: unspecified" in attr
    assert "tests/test_canonical_reports.py: merge: unspecified" in attr
    assert "docs/source_probe.md: merge: unspecified" in attr
    assert "configs/source_probe.json: merge: unspecified" in attr
    assert "reports/runs/run_probe.json: merge: unspecified" in attr
    assert "reports/source_probe.json: merge: unspecified" in attr


def test_content_conflict_uses_configured_driver_without_unmerged_path(tmp_path: Path) -> None:
    repo = _init_repo(tmp_path)
    canonical = f"{CANONICAL_PREFIX}shared.json"
    _write(repo, canonical, "base\n")
    _commit(repo, "seed canonical")
    _install_driver(repo)

    _checkout_branch(repo, "left")
    _write(repo, canonical, "left\n")
    _commit(repo, "left canonical")

    _checkout_branch(repo, "right", "main")
    _write(repo, canonical, "right\n")
    _commit(repo, "right canonical")

    _git(repo, "checkout", "-q", "left")
    merge = _merge(repo, "right")
    assert merge.returncode == 0
    assert canonical not in _unmerged_paths(repo)
    assert _read(repo, canonical) == "left\n"
    policy = policy_module.CanonicalGeneratedMergePolicy(repo)
    assert policy.driver_marked_paths() == [canonical]
    policy.clear_driver_marker()
    assert policy.driver_marked_paths() == []


def test_add_add_canonical_conflict_collapses_to_stage_two(tmp_path: Path) -> None:
    repo = _init_repo(tmp_path)
    canonical = f"{CANONICAL_PREFIX}new.json"

    _checkout_branch(repo, "left")
    _write(repo, canonical, "left\n")
    _commit(repo, "left canonical")

    _checkout_branch(repo, "right", "main")
    _write(repo, canonical, "right\n")
    _commit(repo, "right canonical")

    _git(repo, "checkout", "-q", "left")
    _git(repo, "config", "--unset", "merge.bedc-quality-canonical-generated.driver", check=False)
    merge = _merge(repo, "right")
    assert merge.returncode != 0
    assert _unmerged_paths(repo) == [canonical]

    collapsed = policy_module.CanonicalGeneratedMergePolicy(repo).collapse_unmerged()
    assert [(row.path, row.stage) for row in collapsed] == [(canonical, 2)]
    assert _unmerged_paths(repo) == []
    assert _read(repo, canonical) == "left\n"


def test_modify_delete_and_delete_modify_stage_existing_side(tmp_path: Path) -> None:
    repo = _init_repo(tmp_path)
    canonical = f"{CANONICAL_PREFIX}deleted.json"
    _write(repo, canonical, "base\n")
    _commit(repo, "seed canonical")

    _checkout_branch(repo, "left")
    _write(repo, canonical, "left\n")
    _commit(repo, "left edits")

    _checkout_branch(repo, "right", "main")
    (repo / canonical).unlink()
    _commit(repo, "right deletes")

    _git(repo, "checkout", "-q", "left")
    merge = _merge(repo, "right")
    assert merge.returncode != 0
    collapsed = policy_module.CanonicalGeneratedMergePolicy(repo).collapse_unmerged()
    assert [(row.path, row.stage) for row in collapsed] == [(canonical, 2)]
    assert _read(repo, canonical) == "left\n"

    _git(repo, "merge", "--abort", check=False)
    _git(repo, "checkout", "-q", "right")
    merge = _merge(repo, "left")
    assert merge.returncode != 0
    collapsed = policy_module.CanonicalGeneratedMergePolicy(repo).collapse_unmerged()
    assert [(row.path, row.stage) for row in collapsed] == [(canonical, 3)]
    assert _read(repo, canonical) == "left\n"


def test_rename_delete_canonical_conflict_collapses_only_canonical_path(tmp_path: Path) -> None:
    repo = _init_repo(tmp_path)
    old = f"{CANONICAL_PREFIX}old.json"
    new = f"{CANONICAL_PREFIX}new.json"
    _write(repo, old, "base\n")
    _commit(repo, "seed canonical")

    _checkout_branch(repo, "left")
    _git(repo, "mv", old, new)
    _commit(repo, "left renames")

    _checkout_branch(repo, "right", "main")
    (repo / old).unlink()
    _commit(repo, "right deletes")

    _git(repo, "checkout", "-q", "left")
    merge = _merge(repo, "right")
    assert merge.returncode != 0
    before = _unmerged_paths(repo)
    assert old in before or new in before

    policy_module.CanonicalGeneratedMergePolicy(repo).collapse_unmerged()
    assert _unmerged_paths(repo) == []


def test_mode_only_canonical_index_entry_collapses_when_exposed(tmp_path: Path) -> None:
    repo = _init_repo(tmp_path)
    canonical = f"{CANONICAL_PREFIX}mode.json"
    _write(repo, canonical, "base\n")
    _commit(repo, "seed canonical")

    base_oid = _git(repo, "hash-object", "-w", "--stdin", input_text="base\n").stdout.strip()
    left_oid = _git(repo, "hash-object", "-w", "--stdin", input_text="left\n").stdout.strip()
    right_oid = _git(repo, "hash-object", "-w", "--stdin", input_text="right\n").stdout.strip()
    _git(
        repo,
        "update-index",
        "--index-info",
        input_text=(
            f"100644 {base_oid} 1\t{canonical}\n"
            f"100755 {left_oid} 2\t{canonical}\n"
            f"100644 {right_oid} 3\t{canonical}\n"
        ),
    )

    assert _unmerged_paths(repo) == [canonical]
    collapsed = policy_module.CanonicalGeneratedMergePolicy(repo).collapse_unmerged()
    assert [(row.path, row.stage) for row in collapsed] == [(canonical, 2)]
    assert _unmerged_paths(repo) == []
    assert _read(repo, canonical) == "left\n"
    index_row = _git(repo, "ls-files", "-s", "--", canonical).stdout.strip()
    assert index_row.startswith("100755 ")


def test_source_conflict_remains_unmerged(tmp_path: Path) -> None:
    repo = _init_repo(tmp_path)
    source = "papers/bedc-quality-lab/bedc_quality_lab/source_probe.py"
    _write(repo, source, "base\n")
    _commit(repo, "seed source")

    _checkout_branch(repo, "left")
    _write(repo, source, "left\n")
    _commit(repo, "left source")

    _checkout_branch(repo, "right", "main")
    _write(repo, source, "right\n")
    _commit(repo, "right source")

    _git(repo, "checkout", "-q", "left")
    merge = _merge(repo, "right")
    assert merge.returncode != 0

    collapsed = policy_module.CanonicalGeneratedMergePolicy(repo).collapse_unmerged()
    assert collapsed == []
    assert _unmerged_paths(repo) == [source]


def test_mixed_conflict_collapses_canonical_and_leaves_source(tmp_path: Path) -> None:
    repo = _init_repo(tmp_path)
    canonical = f"{CANONICAL_PREFIX}mixed.json"
    source = "papers/bedc-quality-lab/bedc_quality_lab/source_probe.py"
    _write(repo, ".gitattributes", "")
    _write(repo, canonical, "base\n")
    _write(repo, source, "base\n")
    _commit(repo, "seed mixed")

    _checkout_branch(repo, "left")
    _write(repo, canonical, "left\n")
    _write(repo, source, "left\n")
    _commit(repo, "left mixed")

    _checkout_branch(repo, "right", "main")
    _write(repo, canonical, "right\n")
    _write(repo, source, "right\n")
    _commit(repo, "right mixed")

    _git(repo, "checkout", "-q", "left")
    merge = _merge(repo, "right")
    assert merge.returncode != 0
    assert sorted(_unmerged_paths(repo)) == sorted([canonical, source])

    policy_module.CanonicalGeneratedMergePolicy(repo).collapse_unmerged()
    assert _unmerged_paths(repo) == [source]
