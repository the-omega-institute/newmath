#!/usr/bin/env python3
"""Git merge helper for BEDC quality-lab canonical generated artifacts."""

from __future__ import annotations

import argparse
import shlex
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path


DRIVER = "bedc-quality-canonical-generated"
DRIVER_NAME = "BEDC quality-lab canonical generated artifacts"
DRIVER_MARKER = "bedc-quality-canonical-generated-merge.paths"
DRIVER_COMMAND = (
    f"python3 {shlex.quote(str(Path(__file__).resolve()))} driver --repo . %P"
)
CANONICAL_PREFIX = "papers/bedc-quality-lab/reports/canonical/"
CANONICAL_PROBE = f"{CANONICAL_PREFIX}index.json"
UNSCOPED_ATTRIBUTE_PROBES = (
    "papers/bedc-quality-lab/bedc_quality_lab/source_probe.py",
    "papers/bedc-quality-lab/scripts/run_canonical_reports.py",
    "papers/bedc-quality-lab/tests/test_canonical_reports.py",
    "papers/bedc-quality-lab/docs/source_probe.md",
    "papers/bedc-quality-lab/configs/source_probe.json",
    "papers/bedc-quality-lab/reports/runs/run_probe.json",
    "papers/bedc-quality-lab/reports/source_probe.json",
)


class PolicyError(RuntimeError):
    """Raised when the generated-artifact merge policy cannot be applied."""


@dataclass(frozen=True)
class UnmergedEntry:
    mode: str
    oid: str
    stage: int
    path: str


@dataclass(frozen=True)
class CollapsedPath:
    path: str
    stage: int
    oid: str


def _run(
    args: list[str],
    *,
    repo: Path,
    check: bool = True,
    capture: bool = True,
) -> subprocess.CompletedProcess[str]:
    res = subprocess.run(
        args,
        cwd=repo,
        text=True,
        capture_output=capture,
    )
    if check and res.returncode != 0:
        out = ((res.stdout or "") + (res.stderr or "")).strip()
        raise PolicyError(f"command failed ({res.returncode}): {' '.join(args)}\n{out}")
    return res


def _repo_root(repo: Path) -> Path:
    candidate = repo.resolve()
    res = _run(
        ["git", "rev-parse", "--show-toplevel"],
        repo=candidate,
        check=False,
    )
    if res.returncode != 0:
        raise PolicyError(f"not a Git repository: {candidate}")
    return Path(res.stdout.strip()).resolve()


def _git_dir(repo: Path) -> Path:
    res = _run(["git", "rev-parse", "--git-dir"], repo=repo, check=False)
    if res.returncode != 0 or not res.stdout.strip():
        raise PolicyError(f"not a Git repository: {repo}")
    path = Path(res.stdout.strip())
    if not path.is_absolute():
        path = (repo / path).resolve()
    return path


def _parse_unmerged(stdout: str) -> dict[str, list[UnmergedEntry]]:
    grouped: dict[str, list[UnmergedEntry]] = {}
    for raw in stdout.splitlines():
        if not raw:
            continue
        try:
            meta, path = raw.split("\t", 1)
            mode, oid, stage_raw = meta.split(" ", 2)
            stage = int(stage_raw)
        except ValueError as exc:
            raise PolicyError(f"could not parse unmerged index row: {raw!r}") from exc
        grouped.setdefault(path, []).append(UnmergedEntry(mode, oid, stage, path))
    return grouped


def _selected_side(entries: list[UnmergedEntry]) -> UnmergedEntry | None:
    by_stage = {entry.stage: entry for entry in entries}
    return by_stage.get(2) or by_stage.get(3)


class CanonicalGeneratedMergePolicy:
    """Local Git policy for producer-owned canonical report paths."""

    def __init__(self, repo: Path | str = ".") -> None:
        self.repo = _repo_root(Path(repo))

    def install_driver(self, *, check: bool = False) -> None:
        if check:
            self.check_driver()
            self.check_attributes()
            print(f"[canonical-generated-merge] driver and attributes are aligned in {self.repo}")
            return
        _run(
            ["git", "config", "--local", f"merge.{DRIVER}.name", DRIVER_NAME],
            repo=self.repo,
        )
        _run(
            ["git", "config", "--local", f"merge.{DRIVER}.driver", DRIVER_COMMAND],
            repo=self.repo,
        )
        print(f"[canonical-generated-merge] installed {DRIVER} in {self.repo}")

    def check_driver(self) -> None:
        name = _run(
            ["git", "config", "--local", "--get", f"merge.{DRIVER}.name"],
            repo=self.repo,
            check=False,
        )
        driver = _run(
            ["git", "config", "--local", "--get", f"merge.{DRIVER}.driver"],
            repo=self.repo,
            check=False,
        )
        errors: list[str] = []
        if name.returncode != 0 or name.stdout.strip() != DRIVER_NAME:
            errors.append(f"merge.{DRIVER}.name")
        if driver.returncode != 0 or driver.stdout.strip() != DRIVER_COMMAND:
            errors.append(f"merge.{DRIVER}.driver")
        if errors:
            raise PolicyError("Git merge driver config drift: " + ", ".join(errors))

    def check_attributes(self) -> None:
        expected = {CANONICAL_PROBE: DRIVER}
        expected.update({path: "unspecified" for path in UNSCOPED_ATTRIBUTE_PROBES})
        paths = list(expected)
        res = _run(["git", "check-attr", "merge", "--", *paths], repo=self.repo)
        observed: dict[str, str] = {}
        for line in res.stdout.splitlines():
            try:
                path, attr, value = line.split(": ", 2)
            except ValueError as exc:
                raise PolicyError(f"could not parse check-attr row: {line!r}") from exc
            if attr == "merge":
                observed[path] = value
        errors = [
            f"{path} expected {value!r}, observed {observed.get(path)!r}"
            for path, value in expected.items()
            if observed.get(path) != value
        ]
        if errors:
            raise PolicyError("Git attribute policy drift: " + "; ".join(errors))

    def driver_marker_path(self) -> Path:
        return _git_dir(self.repo) / DRIVER_MARKER

    def clear_driver_marker(self) -> None:
        path = self.driver_marker_path()
        try:
            path.unlink()
        except FileNotFoundError:
            return

    def driver_marked_paths(self) -> list[str]:
        path = self.driver_marker_path()
        try:
            rows = path.read_text(encoding="utf-8").splitlines()
        except FileNotFoundError:
            return []
        return [
            row for row in dict.fromkeys(line.strip() for line in rows)
            if row.startswith(CANONICAL_PREFIX)
        ]

    def mark_driver_path(self, path: str) -> None:
        marker = self.driver_marker_path()
        marker.parent.mkdir(parents=True, exist_ok=True)
        with marker.open("a", encoding="utf-8") as fh:
            fh.write(f"{path}\n")

    def unmerged_paths(self) -> dict[str, list[UnmergedEntry]]:
        res = _run(["git", "ls-files", "-u"], repo=self.repo)
        return _parse_unmerged(res.stdout)

    def collapse_unmerged(self) -> list[CollapsedPath]:
        grouped = self.unmerged_paths()
        collapsed: list[CollapsedPath] = []
        for path in sorted(grouped):
            if not path.startswith(CANONICAL_PREFIX):
                continue
            selected = _selected_side(grouped[path])
            if selected is None:
                print(
                    f"[canonical-generated-merge] skipped {path}: no stage 2 or stage 3 side",
                    file=sys.stderr,
                )
                continue
            _run(
                ["git", "checkout-index", f"--stage={selected.stage}", "--force", "--", path],
                repo=self.repo,
            )
            _run(["git", "update-index", "--force-remove", "--", path], repo=self.repo)
            _run(
                ["git", "update-index", "--add", "--cacheinfo", f"{selected.mode},{selected.oid},{path}"],
                repo=self.repo,
            )
            collapsed.append(CollapsedPath(path=path, stage=selected.stage, oid=selected.oid))

        if collapsed:
            for row in collapsed:
                print(
                    f"[canonical-generated-merge] collapsed {row.path} "
                    f"from stage {row.stage} ({row.oid[:12]})"
                )
        else:
            print("[canonical-generated-merge] no canonical unmerged paths")
        return collapsed


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    install = sub.add_parser("install-driver", help="Install or check the local Git merge driver")
    install.add_argument("--repo", default=".", help="Git repository path")
    install.add_argument("--check", action="store_true", help="Check driver and attribute alignment")

    collapse = sub.add_parser("collapse-unmerged", help="Collapse unmerged canonical generated paths")
    collapse.add_argument("--repo", default=".", help="Git repository path")

    driver = sub.add_parser("driver", help="Record a custom-driver placeholder path")
    driver.add_argument("--repo", default=".", help="Git repository path")
    driver.add_argument("path", nargs="?", default="")
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)
    try:
        policy = CanonicalGeneratedMergePolicy(args.repo)
        if args.command == "install-driver":
            policy.install_driver(check=args.check)
            return 0
        if args.command == "collapse-unmerged":
            policy.collapse_unmerged()
            return 0
        if args.command == "driver":
            path = args.path
            if path.startswith(CANONICAL_PREFIX):
                policy.mark_driver_path(path)
            return 0
    except PolicyError as exc:
        print(f"[canonical-generated-merge] {exc}", file=sys.stderr)
        return 2
    parser.error(f"unknown command: {args.command}")
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
