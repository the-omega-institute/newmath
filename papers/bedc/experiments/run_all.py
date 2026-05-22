#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent
CACHE_ROOT = ROOT / "cache" / "run_all"
CACHE_VERSION = "run-all-cache-1"


def file_digest(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def script_dependencies(script: Path) -> tuple[Path, ...]:
    dependencies = [script]
    ncbi_cache = ROOT / "cache" / "ncbi_genetic_codes.html"
    if script.name == "codon_window_spectra.py" and ncbi_cache.exists():
        dependencies.append(ncbi_cache)
    return tuple(dependencies)


def cache_key(script: Path) -> str:
    payload = {
        "cache_version": CACHE_VERSION,
        "python": sys.version_info[:3],
        "script": script.name,
        "dependencies": [
            {
                "path": str(path.relative_to(ROOT)),
                "sha256": file_digest(path),
            }
            for path in script_dependencies(script)
        ],
    }
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def run_script(script: Path) -> int:
    key = cache_key(script)
    cache_path = CACHE_ROOT / f"{script.stem}-{key}.json"
    if cache_path.exists():
        cached = json.loads(cache_path.read_text(encoding="utf-8"))
        sys.stdout.write(cached["stdout"])
        sys.stderr.write(cached["stderr"])
        return int(cached["returncode"])

    result = subprocess.run(
        [sys.executable, str(script)],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )
    sys.stdout.write(result.stdout)
    sys.stderr.write(result.stderr)
    if result.returncode == 0:
        CACHE_ROOT.mkdir(parents=True, exist_ok=True)
        cache_path.write_text(
            json.dumps(
                {
                    "script": script.name,
                    "returncode": result.returncode,
                    "stdout": result.stdout,
                    "stderr": result.stderr,
                },
                sort_keys=True,
            ),
            encoding="utf-8",
        )
    return result.returncode


def main() -> int:
    scripts = [ROOT / "codon_window_spectra.py"]
    for script in scripts:
        returncode = run_script(script)
        if returncode != 0:
            return returncode
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
