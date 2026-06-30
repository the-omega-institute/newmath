#!/usr/bin/env bash
# Warm a bridge worktree's .lake cache — mirrors lean4/scripts/codex_formalize.py
# `_clone_lake_cache`. The bridge depends on mathlib (4.2G of oleans), so a cold
# build is 30-60min. Naively symlinking the WHOLE .lake into a worktree is
# path-sensitive: lake regenerates the per-tree setup metadata with the new
# worktree path, invalidates every cached .olean reference, and rebuilds all of
# mathlib. The proven fix: symlink ONLY `packages/` (external deps never change
# and their absolute paths stay valid when shared at the same location) and
# APFS-clone (cp -Rc, copy-on-write) `build/` + `config/` (small, round-local,
# writable) so lake only recompiles the 2-3 new bridge files.
#
# Usage: clone_lake_cache.sh <dst_worktree_root> [<src_main_repo_root>]
#   <dst_worktree_root>   : the worktree's repo root (contains papers/...).
#   <src_main_repo_root>  : main checkout whose warm bridge .lake to clone from.
#                           Defaults to the first `git worktree list` entry
#                           (the main checkout).
set -euo pipefail

DST_ROOT="${1:?usage: clone_lake_cache.sh <dst_worktree_root> [<src_main_repo_root>]}"
SRC_ROOT="${2:-}"
REL="papers/bedc_mathlib_bridge/lean4/.lake"

if [ -z "$SRC_ROOT" ]; then
  # First `git worktree list` line is the main checkout.
  SRC_ROOT="$(git -C "$DST_ROOT" worktree list 2>/dev/null | head -1 | awk '{print $1}')"
fi

SRC="$SRC_ROOT/$REL"
DST="$DST_ROOT/$REL"

if [ ! -d "$SRC" ]; then
  echo "[bridge-cache] no source .lake at $SRC — skip (cold build will run)"; exit 0
fi
if [ -e "$DST" ] || [ -L "$DST" ]; then
  echo "[bridge-cache] dst .lake already present at $DST — removing for clean clone"
  rm -rf "$DST"
fi

mkdir -p "$DST"

# 1. Symlink packages/ → main's (mathlib; preserves absolute olean paths so lake
#    does NOT invalidate the cache). NEVER copy or symlink the whole .lake.
if [ -d "$SRC/packages" ]; then
  ln -s "$SRC/packages" "$DST/packages"
  echo "[bridge-cache] symlinked packages/ (mathlib, shared read-only)"
fi

# 2. APFS-clone build/ + config/ (round-local writable copies; lake incrementally
#    updates these for the new bridge files only).
for sub in build config; do
  if [ -d "$SRC/$sub" ]; then
    if cp -Rc "$SRC/$sub" "$DST/$sub" 2>/dev/null; then
      echo "[bridge-cache] APFS-cloned $sub/"
    else
      rm -rf "$DST/$sub"
      cp -R "$SRC/$sub" "$DST/$sub"
      echo "[bridge-cache] regular-copied $sub/ (APFS clone unavailable)"
    fi
  fi
done

echo "[bridge-cache] warm cache ready at $DST — next 'lake build' is incremental"
