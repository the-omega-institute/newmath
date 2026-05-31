from __future__ import annotations

import os
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
                "or pass an explicit default/argument"
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
    env: Mapping[str, str] | None = os.environ,
    defaults: Mapping[str, str | Path] | None = None,
    overrides: Mapping[str, str | Path | None] | None = None,
) -> HostContext:
    root = Path(repo_root).resolve() if repo_root is not None else discover_repo_root()
    values: dict[str, str] = {"REPO_ROOT": str(root)}
    if defaults:
        values.update({key: str(value) for key, value in defaults.items()})

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
    _ = env_file
    defaults = {key: str(default)} if default is not None else None
    context = load_host_context(
        repo_root=repo_root,
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
    _ = env_file
    defaults = {key: str(default)} if default is not None else None
    context = load_host_context(
        repo_root=repo_root,
        env=env,
        defaults=defaults,
        overrides={key: explicit},
    )
    if required:
        return context.path(key)
    if context.get(key) is None:
        return None
    return context.path(key)
