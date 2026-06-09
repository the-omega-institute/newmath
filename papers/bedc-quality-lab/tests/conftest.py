from __future__ import annotations

import sys
from pathlib import Path

import pytest


LAB_ROOT = Path(__file__).resolve().parents[1]
if str(LAB_ROOT) not in sys.path:
    sys.path.insert(0, str(LAB_ROOT))


@pytest.fixture(autouse=True)
def lab_working_directory(monkeypatch):
    monkeypatch.chdir(LAB_ROOT)
