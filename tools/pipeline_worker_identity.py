from __future__ import annotations

import json
import re
import secrets
import string
from dataclasses import asdict, dataclass
from pathlib import Path


FORBIDDEN_GENERATED_RE = re.compile(
    r"\b[RP][0-9]+\b|round_R|paper_P|codex-R|paper-P|Round"
)
ITERATION_SLUG_RE = re.compile(
    r"^(?:[rp][0-9]+|r-[0-9]+|p-[0-9]+|round-[0-9]+|round-[rp]?[0-9]+|paper-[0-9]+|paper-[rp]?[0-9]+)$"
)
LEGACY_FORMALIZE_WORKTREE_RE = re.compile(r"^round_R([0-9]+)$")
LEGACY_PAPER_WORKTREE_RE = re.compile(r"^paper_P([0-9]+)$")
LEGACY_FORMALIZE_BRANCH_RE = re.compile(r"^codex-R([0-9]+)$")
LEGACY_PAPER_BRANCH_RE = re.compile(r"^paper-P([0-9]+)$")
LEGACY_TICKET_RE = re.compile(r"^([RP])([0-9]+)_[0-9]+\.json$")


@dataclass(frozen=True)
class WorkerLease:
    kind: str
    semantic_slug: str
    lease_id: str
    display_ordinal: int | None = None
    branch: str = ""
    worktree_name: str = ""
    worktree: Path | None = None
    ticket_stem: str = ""
    log_tag: str = ""
    commit_prefix: str = ""
    holder: str = ""

    def metadata(self) -> dict:
        data = asdict(self)
        if self.worktree is not None:
            data["worktree"] = str(self.worktree)
        return data

    def write_metadata(self, path: Path) -> None:
        path.write_text(json.dumps(self.metadata(), indent=2, sort_keys=True), encoding="utf-8")


def sanitize_slug(raw: str | None, *, fallback: str) -> str:
    if raw and FORBIDDEN_GENERATED_RE.search(raw):
        raise ValueError(f"worker slug uses forbidden iteration form: {raw!r}")
    base = (raw or "").strip().lower()
    base = re.sub(r"[^a-z0-9]+", "-", base)
    base = re.sub(r"-+", "-", base).strip("-")
    slug = base or fallback
    if ITERATION_SLUG_RE.fullmatch(slug):
        raise ValueError(f"iteration-shaped worker slug is not allowed: {raw!r}")
    _reject_forbidden(slug)
    return slug


def allocate_lease_id(existing: set[str] | None = None, *, length: int = 8) -> str:
    alphabet = string.ascii_lowercase + string.digits
    taken = existing or set()
    while True:
        token = "w" + "".join(secrets.choice(alphabet) for _ in range(max(1, length - 1)))
        if token not in taken and not ITERATION_SLUG_RE.fullmatch(token):
            return token


def new_worker_lease(
    kind: str,
    semantic_slug: str | None = None,
    *,
    display_ordinal: int | None = None,
    lease_id: str | None = None,
    worktree_dir: Path | None = None,
) -> WorkerLease:
    if kind not in {"formalize", "paper-revise"}:
        raise ValueError(f"unknown worker kind: {kind!r}")
    slug = sanitize_slug(semantic_slug, fallback=kind)
    lease = lease_id or allocate_lease_id()
    if not re.fullmatch(r"[a-z][a-z0-9]{3,15}", lease):
        raise ValueError(f"invalid lease id: {lease!r}")
    if kind == "formalize":
        branch = f"formalize-{slug}-{lease}"
        worktree_name = f"formalize_{slug.replace('-', '_')}_{lease}"
    else:
        branch = f"paper-revise-{slug}-{lease}"
        worktree_name = f"paper_revise_{slug.replace('-', '_')}_{lease}"
    holder = f"{kind}-{slug}-{lease}"
    ticket_stem = f"{worktree_name}_{lease}"
    log_tag = worktree_name
    commit_prefix = f"{holder}:"
    generated = [branch, worktree_name, ticket_stem, log_tag, commit_prefix, holder]
    for value in generated:
        _reject_forbidden(value)
    worktree = worktree_dir / worktree_name if worktree_dir is not None else None
    return WorkerLease(
        kind=kind,
        semantic_slug=slug,
        lease_id=lease,
        display_ordinal=display_ordinal,
        branch=branch,
        worktree_name=worktree_name,
        worktree=worktree,
        ticket_stem=ticket_stem,
        log_tag=log_tag,
        commit_prefix=commit_prefix,
        holder=holder,
    )


def _reject_forbidden(value: str) -> None:
    if FORBIDDEN_GENERATED_RE.search(value):
        raise ValueError(f"generated worker identity uses forbidden iteration form: {value!r}")


def legacy_worktree_kind(name: str) -> tuple[str, int] | None:
    m = LEGACY_FORMALIZE_WORKTREE_RE.fullmatch(name)
    if m:
        return "formalize", int(m.group(1))
    m = LEGACY_PAPER_WORKTREE_RE.fullmatch(name)
    if m:
        return "paper-revise", int(m.group(1))
    return None


def legacy_branch_kind(name: str) -> tuple[str, int] | None:
    m = LEGACY_FORMALIZE_BRANCH_RE.fullmatch(name)
    if m:
        return "formalize", int(m.group(1))
    m = LEGACY_PAPER_BRANCH_RE.fullmatch(name)
    if m:
        return "paper-revise", int(m.group(1))
    return None


def legacy_ticket_kind(name: str) -> tuple[str, int] | None:
    m = LEGACY_TICKET_RE.fullmatch(name)
    if not m:
        return None
    return ("formalize" if m.group(1) == "R" else "paper-revise", int(m.group(2)))


def parse_new_worktree_name(name: str) -> tuple[str, str, str] | None:
    m = re.fullmatch(r"(formalize|paper_revise)_([a-z0-9_]+)_(w[a-z0-9]{3,15})", name)
    if not m:
        return None
    kind = "formalize" if m.group(1) == "formalize" else "paper-revise"
    return kind, m.group(2).replace("_", "-"), m.group(3)
