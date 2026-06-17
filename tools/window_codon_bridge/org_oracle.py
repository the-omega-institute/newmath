#!/usr/bin/env python3
"""Controlled entrypoint for the shared NyxID ChatGPT Pro org pool."""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path


DEFAULT_POOL = "company-chatgpt-pro"
LOCK_ROOT = Path(os.environ.get("NYXID_ORG_ORACLE_LOCK_DIR", "/tmp/nyxid-org-oracle-conv-locks"))


def run(cmd: list[str]) -> int:
    proc = subprocess.run(cmd)
    return proc.returncode


def capture_json(cmd: list[str]) -> dict:
    proc = subprocess.run(cmd, text=True, capture_output=True)
    if proc.returncode != 0:
        if proc.stderr:
            sys.stderr.write(proc.stderr)
        if proc.stdout:
            sys.stderr.write(proc.stdout)
        raise SystemExit(proc.returncode)
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        sys.stderr.write(f"expected JSON from command: {' '.join(cmd)}\n{exc}\n")
        raise SystemExit(2)


def append_common_ask(args: argparse.Namespace, cmd: list[str]) -> list[str]:
    if args.file:
        cmd += ["--file", args.file]
    elif args.prompt:
        cmd.append(args.prompt)
    else:
        cmd += ["--file", "-"]
    if args.pdf:
        cmd += ["--pdf", args.pdf]
    if args.model:
        cmd += ["--model", args.model]
    if args.project_url:
        cmd += ["--project-url", args.project_url]
    if args.tag:
        cmd += ["--tag", args.tag]
    if args.client_ref:
        cmd += ["--client-ref", args.client_ref]
    if args.no_wait:
        cmd.append("--no-wait")
    else:
        cmd += ["--wait", str(args.wait)]
    cmd += ["--output", args.output]
    return cmd


def lock_path(conversation_id: str) -> Path:
    safe = "".join(c if c.isalnum() or c in "_-" else "_" for c in conversation_id)
    return LOCK_ROOT / f"{safe}.lock"


class ConversationLock:
    def __init__(self, conversation_id: str, disabled: bool = False) -> None:
        self.conversation_id = conversation_id
        self.disabled = disabled
        self.path = lock_path(conversation_id)
        self.acquired = False

    def __enter__(self) -> "ConversationLock":
        if self.disabled:
            return self
        LOCK_ROOT.mkdir(parents=True, exist_ok=True)
        flags = os.O_CREAT | os.O_EXCL | os.O_WRONLY
        try:
            fd = os.open(self.path, flags, 0o600)
        except FileExistsError:
            sys.stderr.write(
                f"conversation {self.conversation_id} is already locked on this machine.\n"
                f"Use `release --conversation {self.conversation_id}` only when the session should be closed,\n"
                f"or remove stale lock: {self.path}\n"
            )
            raise SystemExit(73)
        with os.fdopen(fd, "w") as f:
            f.write(json.dumps({"pid": os.getpid(), "conversation_id": self.conversation_id}) + "\n")
        self.acquired = True
        return self

    def __exit__(self, exc_type, exc, tb) -> None:
        if self.acquired:
            try:
                self.path.unlink()
            except FileNotFoundError:
                pass


def cmd_status(args: argparse.Namespace) -> int:
    return run(["nyxid", "oracle", "status", args.pool, "--output", args.output])


def cmd_new(args: argparse.Namespace) -> int:
    cmd = ["nyxid", "oracle", "ask", args.pool, "--new-conversation"]
    return run(append_common_ask(args, cmd))


def cmd_continue(args: argparse.Namespace) -> int:
    with ConversationLock(args.conversation_id, disabled=args.no_local_lock):
        cmd = ["nyxid", "oracle", "ask", args.pool, "--conversation", args.conversation_id]
        return run(append_common_ask(args, cmd))


def chatgpt_url_for_conversation(conversation_id: str) -> str:
    data = capture_json(["nyxid", "oracle", "session", conversation_id, "--output", "json"])
    url = str(data.get("chatgpt_url") or "")
    if not url:
        sys.stderr.write(
            f"conversation {conversation_id} has no saved chatgpt_url; pass a ChatGPT URL directly.\n"
        )
        raise SystemExit(2)
    return url


def cmd_read_live(args: argparse.Namespace) -> int:
    target = args.target
    if target.startswith("conv_"):
        with ConversationLock(target, disabled=args.no_local_lock):
            target = chatgpt_url_for_conversation(target)
            cmd = ["nyxid", "oracle", "attach", args.pool, target]
            if args.tag:
                cmd += ["--tag", args.tag]
            if args.no_wait:
                cmd.append("--no-wait")
            else:
                cmd += ["--wait", str(args.wait)]
            cmd += ["--output", args.output]
            return run(cmd)
    cmd = ["nyxid", "oracle", "attach", args.pool, target]
    if args.tag:
        cmd += ["--tag", args.tag]
    if args.no_wait:
        cmd.append("--no-wait")
    else:
        cmd += ["--wait", str(args.wait)]
    cmd += ["--output", args.output]
    return run(cmd)


def cmd_read_cache(args: argparse.Namespace) -> int:
    return run(["nyxid", "oracle", "session", args.conversation_id, "--output", args.output])


def cmd_release(args: argparse.Namespace) -> int:
    if args.task_id:
        return run(["nyxid", "oracle", "cancel", args.task_id, "--output", args.output])
    if args.conversation_id:
        lp = lock_path(args.conversation_id)
        if args.clear_local_lock and lp.exists():
            lp.unlink()
        return run(["nyxid", "oracle", "close-session", args.conversation_id, "--output", args.output])
    sys.stderr.write("release requires --task-id or --conversation-id\n")
    return 2


def add_ask_options(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("prompt", nargs="?", help="Prompt text. Omit to read stdin unless --file is set.")
    parser.add_argument("--file", help="Prompt file, or '-' for stdin.")
    parser.add_argument("--pdf", help="PDF attachment path.")
    parser.add_argument("--model", help="Model hint.")
    parser.add_argument("--project-url", help="ChatGPT Project URL.")
    parser.add_argument("--tag", help="Task tag.")
    parser.add_argument("--client-ref", help="Idempotency key.")
    parser.add_argument("--wait", type=int, default=3600)
    parser.add_argument("--no-wait", action="store_true")
    parser.add_argument("--output", choices=["table", "json"], default="table")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=(
            "Mode-gated wrapper for the shared company-chatgpt-pro oracle pool. "
            "Choose exactly one mode: new, continue, read-live, read-cache, release."
        )
    )
    parser.add_argument("--pool", default=DEFAULT_POOL, help=f"Pool slug. Default: {DEFAULT_POOL}")
    sub = parser.add_subparsers(dest="mode", required=True)

    p = sub.add_parser("status", help="Show pool workers and queue.")
    p.add_argument("--output", choices=["table", "json"], default="table")
    p.set_defaults(func=cmd_status)

    p = sub.add_parser("new", help="Start a new multi-turn conversation.")
    add_ask_options(p)
    p.set_defaults(func=cmd_new)

    p = sub.add_parser("continue", help="Continue one existing conversation.")
    p.add_argument("conversation_id")
    p.add_argument("--no-local-lock", action="store_true", help="Disable this machine's guard lock.")
    add_ask_options(p)
    p.set_defaults(func=cmd_continue)

    p = sub.add_parser("read-live", help="Open ChatGPT and import a live transcript; occupies a worker.")
    p.add_argument("target", help="ChatGPT conversation URL, or conv_id with a saved chatgpt_url.")
    p.add_argument("--tag")
    p.add_argument("--wait", type=int, default=120)
    p.add_argument("--no-wait", action="store_true")
    p.add_argument("--no-local-lock", action="store_true", help="Disable this machine's guard lock for conv_id targets.")
    p.add_argument("--output", choices=["table", "json"], default="table")
    p.set_defaults(func=cmd_read_live)

    p = sub.add_parser("read-cache", help="Read the NyxID cached transcript; does not occupy a worker.")
    p.add_argument("conversation_id")
    p.add_argument("--output", choices=["table", "json"], default="table")
    p.set_defaults(func=cmd_read_cache)

    p = sub.add_parser("release", help="Release a task or close a conversation.")
    group = p.add_mutually_exclusive_group(required=True)
    group.add_argument("--task-id", help="Cancel a queued or in-flight task.")
    group.add_argument("--conversation-id", help="Close a conversation.")
    p.add_argument("--clear-local-lock", action="store_true", help="Remove a stale local lock for --conversation-id.")
    p.add_argument("--output", choices=["table", "json"], default="table")
    p.set_defaults(func=cmd_release)

    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args) or 0)


if __name__ == "__main__":
    raise SystemExit(main())
