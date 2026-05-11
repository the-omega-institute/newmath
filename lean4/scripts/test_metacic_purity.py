#!/usr/bin/env python3
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
CMD = [sys.executable, str(REPO / "lean4/scripts/bedc_ci.py"), "metacic-purity"]


def main() -> int:
    result = subprocess.run(CMD, capture_output=True, text=True, cwd=REPO)
    assert result.returncode == 0, f"exit {result.returncode}: {result.stderr}"
    assert "metacic-purity report" in result.stdout
    assert "BEDC.MetaCIC." in result.stdout
    assert "total:" in result.stdout
    assert "violations:" in result.stdout
    strict = subprocess.run(CMD + ["--strict"], capture_output=True, text=True, cwd=REPO)
    assert strict.returncode == 0, f"strict exit {strict.returncode}: {strict.stdout}\n{strict.stderr}"
    assert "violations: 0" in strict.stdout
    print("OK: metacic-purity sanity test passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
