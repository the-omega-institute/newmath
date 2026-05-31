from __future__ import annotations

import os
import shlex
from dataclasses import dataclass
from pathlib import Path
from typing import Mapping


class MissingHostValueError(RuntimeError):
    pass


def discover_repo_root(start: str | Path | None = None) -> Path:
    here = Path(start).resolve() if start is not None else Path(__file__).resolve()
    candidates = [here] if here.is_dir() else [here.parent]
    candidates.extend(candidates[0].parents)
    for candidate in candidates:
        if (candidate / ".git").exists():
            return candidate
    return Path(__file__).resolve().parent.parent


def _parse_value(raw: str) -> str:
    if raw == "":
        return ""
    try:
        parts = shlex.split(raw, comments=True, posix=True)
    except ValueError:
        return raw.strip().strip("'\"")
    if not parts:
        return ""
    return " ".join(parts)


def parse_host_env_text(text: str) -> dict[str, str]:
    values: dict[str, str] = {}
    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("export "):
            line = line[len("export "):].lstrip()
        key, sep, value = line.partition("=")
        if not sep:
            continue
        key = key.strip()
        if not key or not key.replace("_", "").isalnum() or key[0].isdigit():
            continue
        values[key] = _parse_value(value.strip())
    return values


def read_host_env(path: str | Path) -> dict[str, str]:
    env_path = Path(path)
    try:
        return parse_host_env_text(env_path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return {}


def host_env_candidates(repo_root: str | Path) -> list[Path]:
    root = Path(repo_root).resolve()
    candidates = [root / ".bedc" / "host.env"]
    git_file = root / ".git"
    if git_file.is_file():
        try:
            text = git_file.read_text(encoding="utf-8", errors="ignore").strip()
        except OSError:
            text = ""
        prefix = "gitdir:"
        if text.startswith(prefix):
            git_dir = Path(text[len(prefix):].strip())
            if not git_dir.is_absolute():
                git_dir = (root / git_dir).resolve()
            common = git_dir.parent.parent.parent
            candidates.append(common / ".bedc" / "host.env")
    out: list[Path] = []
    seen: set[Path] = set()
    for candidate in candidates:
        resolved = candidate.resolve()
        if resolved not in seen:
            out.append(resolved)
            seen.add(resolved)
    return out


@dataclass(frozen=True)
class HostContext:
    values: Mapping[str, str]

    def get(self, key: str, default: str | None = None) -> str | None:
        return self.values.get(key, default)

    def require(self, key: str) -> str:
        value = self.get(key)
        if value is None:
            raise MissingHostValueError(
                f"Missing required host key {key}; set it in the process environment "
                "or .bedc/host.env"
            )
        return value

    def path(self, key: str, default: str | Path | None = None) -> Path:
        raw = self.get(key, None if default is None else str(default))
        if raw is None:
            raise KeyError(key)
        expanded = Path(os.path.expandvars(raw)).expanduser()
        if expanded.is_absolute():
            return expanded
        if key == "REPO_ROOT":
            return expanded.resolve()
        root = Path(os.path.expandvars(self.require("REPO_ROOT"))).expanduser()
        if not root.is_absolute():
            root = root.resolve()
        return (root / expanded).resolve()


def load_host_context(
    *,
    repo_root: str | Path | None = None,
    env_file: str | Path | None = None,
    env: Mapping[str, str] | None = os.environ,
    defaults: Mapping[str, str | Path] | None = None,
    overrides: Mapping[str, str | Path | None] | None = None,
) -> HostContext:
    root = Path(repo_root).resolve() if repo_root is not None else discover_repo_root()
    values: dict[str, str] = {"REPO_ROOT": str(root)}
    if defaults:
        values.update({key: str(value) for key, value in defaults.items()})

    if env_file is not None:
        values.update(read_host_env(env_file))
    else:
        for candidate in host_env_candidates(values["REPO_ROOT"]):
            env_values = read_host_env(candidate)
            if env_values:
                values.update(env_values)
                break

    if env is not None:
        values.update({key: value for key, value in env.items() if value is not None})

    if overrides:
        values.update({key: str(value) for key, value in overrides.items() if value is not None})

    if "REPO_ROOT" in values:
        values["REPO_ROOT"] = str(Path(os.path.expandvars(values["REPO_ROOT"])).expanduser().resolve())
    return HostContext(values)


def host_value(
    repo_root: str | Path | None,
    key: str,
    *,
    explicit: str | Path | None = None,
    default: str | Path | None = None,
    env_file: str | Path | None = None,
    env: Mapping[str, str] | None = os.environ,
    required: bool = False,
) -> str | None:
    defaults = {key: str(default)} if default is not None else None
    context = load_host_context(
        repo_root=repo_root,
        env_file=env_file,
        env=env,
        defaults=defaults,
        overrides={key: explicit},
    )
    if required:
        return context.require(key)
    return context.get(key, None if default is None else str(default))


def host_path(
    repo_root: str | Path | None,
    key: str,
    *,
    explicit: str | Path | None = None,
    default: str | Path | None = None,
    env_file: str | Path | None = None,
    env: Mapping[str, str] | None = os.environ,
    required: bool = False,
) -> Path | None:
    defaults = {key: str(default)} if default is not None else None
    context = load_host_context(
        repo_root=repo_root,
        env_file=env_file,
        env=env,
        defaults=defaults,
        overrides={key: explicit},
    )
    if required:
        return context.path(key)
    if context.get(key) is None:
        return None
    return context.path(key)
