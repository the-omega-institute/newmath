from __future__ import annotations

import json
from pathlib import Path

from huggingface_hub import HfApi


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT / "reports"
OUT = REPORT_DIR / "lewm_cross_env_assets.json"

TARGET_ENVS = ("pusht", "reacher", "cube")


def sibling_rows(info) -> list[dict[str, object]]:
    rows = []
    for s in info.siblings:
        rows.append({"name": s.rfilename, "size": s.size})
    return rows


def main() -> None:
    REPORT_DIR.mkdir(exist_ok=True)
    api = HfApi()
    all_models = sorted(m.modelId for m in api.list_models(author="quentinll", search="lewm"))
    all_datasets = sorted(d.id for d in api.list_datasets(author="quentinll", search="lewm"))

    envs: dict[str, dict[str, object]] = {}
    for env in TARGET_ENVS:
        model_repo = f"quentinll/lewm-{env}"
        dataset_repo = f"quentinll/lewm-{env}"
        row: dict[str, object] = {
            "env": env,
            "model_repo": model_repo,
            "dataset_repo": dataset_repo,
            "model_available": False,
            "dataset_available": False,
            "model_files": [],
            "dataset_files": [],
        }
        try:
            row["model_files"] = sibling_rows(api.model_info(model_repo, files_metadata=True))
            row["model_available"] = True
        except Exception as exc:
            row["model_error"] = repr(exc)
        try:
            row["dataset_files"] = sibling_rows(api.dataset_info(dataset_repo, files_metadata=True))
            row["dataset_available"] = True
        except Exception as exc:
            row["dataset_error"] = repr(exc)
        envs[env] = row

    report = {
        "source_inference": {
            "tworooms_prior": {
                "model_repo": "quentinll/lewm-tworooms",
                "dataset_repo": "quentinll/lewm-tworooms",
                "streaming_method": (
                    "HF HfFileSystem remote read of .tar.zst, decompressed as a stream, "
                    "then HDF5 prefix read for early episodes"
                ),
                "evidence_files": [
                    "_phase0_prompt.md",
                    "_phase1a_export_latents.py",
                    "_phase1a_h5_prefix.py",
                    "_phase1a_probe_tar.py",
                    "_phase1a_log.log",
                    "PHASE1A_FINDINGS.md",
                ],
            },
            "cross_env_rule": "infer corresponding dataset repo as quentinll/lewm-<env>; fail-closed if not readable",
        },
        "all_lewm_model_repos_found": all_models,
        "all_lewm_dataset_repos_found": all_datasets,
        "target_envs": list(TARGET_ENVS),
        "envs": envs,
    }
    OUT.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
