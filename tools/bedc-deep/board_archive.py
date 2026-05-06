#!/usr/bin/env python3
"""Active BOARD / completed BOARD archive helpers."""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path

from dispatch_bedc_target import BOARD_PATH, SCRIPT_DIR, BedcTarget, TARGET_HEADER, parse_board
from locks import file_lock


COMPLETED_BOARD_PATH = SCRIPT_DIR / "BOARD.completed.md"
ARCHIVE_HEADER = "# BEDC Deep Reasoning Board Completed Archive\n\n"


@dataclass
class PruneResult:
    moved: int
    active_kept: int
    archive_total: int
    board_path: str
    archive_path: str


def board_paths(include_archive: bool = True) -> list[Path]:
    paths = [BOARD_PATH]
    if include_archive and COMPLETED_BOARD_PATH.exists():
        paths.append(COMPLETED_BOARD_PATH)
    return paths


def parse_board_file(path: Path) -> dict[str, BedcTarget]:
    if not path.exists():
        return {}
    return parse_board(path)


def parse_all_boards(*, include_archive: bool = True) -> dict[str, BedcTarget]:
    targets: dict[str, BedcTarget] = {}
    for path in board_paths(include_archive=include_archive):
        targets.update(parse_board_file(path))
    return targets


def existing_target_ids(*, include_archive: bool = True) -> list[str]:
    ids: list[str] = []
    for path in board_paths(include_archive=include_archive):
        if not path.exists():
            continue
        text = path.read_text(encoding="utf-8")
        ids.extend(re.findall(r"^### (B-\d+)\b", text, flags=re.MULTILINE))
    return ids


def existing_target_titles(*, include_archive: bool = True) -> set[str]:
    titles: set[str] = set()
    for target in parse_all_boards(include_archive=include_archive).values():
        if target.title:
            titles.add(target.title.strip().lower())
    return titles


def completed_state_exists(target: BedcTarget) -> bool:
    return (SCRIPT_DIR / "state" / f"{target.slug}.json").exists()


def _split_board_text(text: str) -> tuple[str, list[tuple[str, str]]]:
    matches = list(TARGET_HEADER.finditer(text))
    if not matches:
        return (text.rstrip() + "\n", [])
    preamble = text[: matches[0].start()].rstrip() + "\n\n"
    blocks: list[tuple[str, str]] = []
    for idx, match in enumerate(matches):
        start = match.start()
        end = matches[idx + 1].start() if idx + 1 < len(matches) else len(text)
        block = text[start:end].strip() + "\n\n"
        blocks.append((match.group(1), block))
    return preamble, blocks


def _write_board(path: Path, preamble: str, blocks: list[str]) -> None:
    body = "".join(blocks).rstrip()
    text = preamble.rstrip() + "\n\n"
    if body:
        text += body + "\n"
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(text, encoding="utf-8")
    tmp.replace(path)


def prune_completed_board() -> PruneResult:
    """Move completed BOARD entries into BOARD.completed.md.

    Completion remains state-file based. This only keeps the active queue small
    while preserving completed ids/titles for deduplication and id allocation.
    """

    with file_lock("board"):
        board_text = BOARD_PATH.read_text(encoding="utf-8") if BOARD_PATH.exists() else ""
        preamble, blocks = _split_board_text(board_text)
        active_targets = parse_board_file(BOARD_PATH)
        archive_targets = parse_board_file(COMPLETED_BOARD_PATH)
        archive_ids = set(archive_targets)

        kept_blocks: list[str] = []
        moved_blocks: list[str] = []
        for target_id, block in blocks:
            target = active_targets.get(target_id)
            if target is not None and completed_state_exists(target):
                if target_id not in archive_ids:
                    moved_blocks.append(block)
                    archive_ids.add(target_id)
                continue
            kept_blocks.append(block)

        if moved_blocks:
            _write_board(BOARD_PATH, preamble, kept_blocks)
            if COMPLETED_BOARD_PATH.exists():
                archive_text = COMPLETED_BOARD_PATH.read_text(encoding="utf-8").rstrip()
                new_archive = archive_text + "\n\n" + "".join(moved_blocks).rstrip() + "\n"
            else:
                new_archive = ARCHIVE_HEADER + "".join(moved_blocks).rstrip() + "\n"
            tmp = COMPLETED_BOARD_PATH.with_suffix(COMPLETED_BOARD_PATH.suffix + ".tmp")
            tmp.write_text(new_archive, encoding="utf-8")
            tmp.replace(COMPLETED_BOARD_PATH)

        archive_total = len(parse_board_file(COMPLETED_BOARD_PATH)) if COMPLETED_BOARD_PATH.exists() else 0
        return PruneResult(
            moved=len(moved_blocks),
            active_kept=len(kept_blocks),
            archive_total=archive_total,
            board_path=str(BOARD_PATH),
            archive_path=str(COMPLETED_BOARD_PATH),
        )


def main() -> int:
    result = prune_completed_board()
    print(
        f"moved={result.moved} active_kept={result.active_kept} "
        f"archive_total={result.archive_total}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
