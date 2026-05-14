#!/usr/bin/env python3
"""Focused checks for the Stage 2 post-write logic surface audit."""

import importlib.util
import sys
from pathlib import Path


MODULE_PATH = Path(__file__).with_name("killo_golden_writeback.py")
spec = importlib.util.spec_from_file_location("killo_golden_writeback", MODULE_PATH)
assert spec is not None and spec.loader is not None
killo_golden_writeback = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = killo_golden_writeback
spec.loader.exec_module(killo_golden_writeback)


def _codes(content: str) -> set[str]:
    audit = killo_golden_writeback._logic_surface_audit(content)
    return {str(w.get("code")) for w in audit.get("warnings", []) if isinstance(w, dict)}


def test_projection_and_unfolding_are_elimination_cues() -> None:
    content = r"""
\begin{theorem}
The transport surface is determined by projection.
\end{theorem}
\begin{proof}
Projecting the witness and unfolding the displayed classifier gives the
same consumer-facing coordinates.
\end{proof}
"""
    assert "bridge_surface_without_elimination_cue" not in _codes(content)


def test_bridge_surface_without_elimination_still_warns() -> None:
    content = r"""
\begin{theorem}
The bridge surface is available.
\end{theorem}
\begin{proof}
The mirror relation is compatible with the ambient object.
\end{proof}
"""
    assert "bridge_surface_without_elimination_cue" in _codes(content)


if __name__ == "__main__":
    test_projection_and_unfolding_are_elimination_cues()
    test_bridge_surface_without_elimination_still_warns()
    print("test_logic_surface_audit: ok")
