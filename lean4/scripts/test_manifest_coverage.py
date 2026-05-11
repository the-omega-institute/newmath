"""Sanity test for `bedc_ci.py manifest-coverage` subcommand."""
import os
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
CMD = [sys.executable, str(REPO / "lean4/scripts/bedc_ci.py"), "manifest-coverage"]


def main() -> int:
    result = subprocess.run(CMD, capture_output=True, text=True, cwd=REPO)
    assert result.returncode == 0, f"exit {result.returncode}: {result.stderr}"
    assert "paper_markers" in result.stdout, f"missing 'paper_markers' in output: {result.stdout[:500]}"
    assert "manifest_entries" in result.stdout, f"missing 'manifest_entries' in output: {result.stdout[:500]}"
    print("OK: manifest-coverage sanity test passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
