#!/usr/bin/env python3
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
CMD = [sys.executable, str(REPO / "lean4/scripts/bedc_ci.py"), "marker-existence-audit"]


def main() -> int:
    r = subprocess.run(CMD, capture_output=True, text=True, cwd=REPO)
    assert r.returncode == 0, f"exit {r.returncode}: {r.stderr}"
    assert "markers_total" in r.stdout
    assert "markers_resolved" in r.stdout
    print("OK: marker-existence-audit sanity test passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
