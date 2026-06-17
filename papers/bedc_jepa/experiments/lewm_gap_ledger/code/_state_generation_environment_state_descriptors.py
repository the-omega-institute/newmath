from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_LATENTS = Path("C:/OMEGA/le-wm-survey/tworooms_latent_large.npz")
DEFAULT_JSON = REPORT_DIR / "state_generation_environment_state_descriptors.json"
DEFAULT_MD = REPORT_DIR / "state_generation_environment_state_descriptors.md"
HARD_DIAGNOSTIC_JSON = REPORT_DIR / "state_generation_hard_episode_diagnostic.json"
BOOTSTRAPS = 5000


def clean_float(value: float) -> float:
    out = float(value)
    if out == 0.0:
        return 0.0
    if not math.isfinite(out):
        raise ValueError(f"non-finite value: {out!r}")
    return out


def clean_json(value: Any) -> Any:
    if isinstance(value, dict):
        return {str(k): clean_json(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [clean_json(v) for v in value]
    if isinstance(value, np.ndarray):
        return clean_json(value.tolist())
    if isinstance(value, (np.integer,)):
        return int(value)
    if isinstance(value, (np.floating,)):
        return clean_float(float(value))
    if isinstance(value, float):
        return clean_float(value)
    return value


def load_npz(path: Path) -> dict[str, np.ndarray]:
    with np.load(path, allow_pickle=False) as data:
        return {key: data[key] for key in data.files}


def read_hard_episodes(path: Path) -> list[int]:
    report = json.loads(path.read_text(encoding="utf-8"))
    episodes = report.get("hard_episode_union", [])
    if not isinstance(episodes, list) or not episodes:
        raise RuntimeError("missing hard episode union")
    return [int(item) for item in episodes]


def episode_groups(episode: np.ndarray) -> list[np.ndarray]:
    return [np.where(episode == ep)[0].astype(np.int64) for ep in np.unique(episode.astype(np.int64))]


def anchor_env_rows(aligned: dict[str, np.ndarray], latents: dict[str, np.ndarray], split: str) -> dict[str, np.ndarray]:
    episode = aligned[f"{split}_episode"].astype(np.int64)
    t0 = aligned[f"{split}_t0"].astype(np.int64)
    idx = np.arange(len(episode), dtype=np.int64)
    next_t = np.minimum(t0 + 1, latents["pos_agent"].shape[1] - 1)
    action = latents["action"][episode, t0].astype(np.float64)
    next_action = latents["action"][episode, next_t].astype(np.float64)
    pos_agent = latents["pos_agent"][episode, t0].astype(np.float64)
    pos_target = latents["pos_target"][episode, t0].astype(np.float64)
    rel = pos_target - pos_agent
    dist = latents["distance_to_target"][episode, t0].astype(np.float64)
    next_dist = latents["distance_to_target"][episode, next_t].astype(np.float64)
    same_room = latents["same_room_lr"][episode, t0].astype(np.float64)
    agent_room = latents["agent_room_lr"][episode, t0].astype(np.float64)
    target_room = latents["target_room_lr"][episode, t0].astype(np.float64)
    crossing = latents["crosses_room_midline"][episode, np.minimum(t0, latents["crosses_room_midline"].shape[1] - 1)].astype(np.float64)
    reward = latents["reward"][episode, t0].astype(np.float64)
    terminated = latents["terminated"][episode, t0].astype(np.float64)
    action_norm = np.linalg.norm(action, axis=1)
    action_delta = np.linalg.norm(next_action - action, axis=1)
    transition_step = np.linalg.norm(
        latents["pos_agent"][episode, next_t].astype(np.float64) - pos_agent,
        axis=1,
    )
    return {
        "episode": episode,
        "row": idx,
        "distance_to_target": dist,
        "next_distance_to_target": next_dist,
        "distance_change": next_dist - dist,
        "agent_x": pos_agent[:, 0],
        "agent_y": pos_agent[:, 1],
        "target_x": pos_target[:, 0],
        "target_y": pos_target[:, 1],
        "relative_x": rel[:, 0],
        "relative_y": rel[:, 1],
        "same_room": same_room,
        "different_room": 1.0 - same_room,
        "agent_room": agent_room,
        "target_room": target_room,
        "crosses_room_midline": crossing,
        "reward": reward,
        "terminated": terminated,
        "action_norm": action_norm,
        "action_delta": action_delta,
        "transition_step": transition_step,
    }


def episode_stat(values: np.ndarray, episode: np.ndarray, stat: str) -> dict[int, float]:
    out: dict[int, float] = {}
    for idxs in episode_groups(episode):
        local = values[idxs].astype(np.float64)
        if stat == "mean":
            value = float(np.mean(local))
        elif stat == "max":
            value = float(np.max(local))
        elif stat == "min":
            value = float(np.min(local))
        elif stat == "std":
            value = float(np.std(local))
        elif stat == "p90":
            value = float(np.percentile(local, 90))
        elif stat == "p10":
            value = float(np.percentile(local, 10))
        else:
            raise ValueError(stat)
        out[int(episode[idxs[0]])] = clean_float(value)
    return out


def build_episode_descriptors(rows: dict[str, np.ndarray]) -> dict[str, dict[int, float]]:
    episode = rows["episode"].astype(np.int64)
    specs = {
        "distance_mean": ("distance_to_target", "mean", "higher"),
        "distance_min": ("distance_to_target", "min", "higher"),
        "distance_p90": ("distance_to_target", "p90", "higher"),
        "distance_change_mean": ("distance_change", "mean", "higher"),
        "agent_x_mean": ("agent_x", "mean", "either"),
        "agent_y_mean": ("agent_y", "mean", "either"),
        "target_x_mean": ("target_x", "mean", "either"),
        "target_y_mean": ("target_y", "mean", "either"),
        "relative_x_mean": ("relative_x", "mean", "either"),
        "relative_y_mean": ("relative_y", "mean", "either"),
        "different_room_mean": ("different_room", "mean", "higher"),
        "same_room_mean": ("same_room", "mean", "lower"),
        "crosses_midline_mean": ("crosses_room_midline", "mean", "higher"),
        "crosses_midline_max": ("crosses_room_midline", "max", "higher"),
        "action_norm_mean": ("action_norm", "mean", "higher"),
        "action_delta_mean": ("action_delta", "mean", "higher"),
        "transition_step_mean": ("transition_step", "mean", "higher"),
        "transition_step_p90": ("transition_step", "p90", "higher"),
        "reward_mean": ("reward", "mean", "lower"),
        "terminated_mean": ("terminated", "mean", "higher"),
    }
    return {name: episode_stat(rows[field], episode, stat) for name, (field, stat, _) in specs.items()}


def descriptor_directions() -> dict[str, str]:
    return {
        "distance_mean": "higher",
        "distance_min": "higher",
        "distance_p90": "higher",
        "distance_change_mean": "higher",
        "agent_x_mean": "either",
        "agent_y_mean": "either",
        "target_x_mean": "either",
        "target_y_mean": "either",
        "relative_x_mean": "either",
        "relative_y_mean": "either",
        "different_room_mean": "higher",
        "same_room_mean": "lower",
        "crosses_midline_mean": "higher",
        "crosses_midline_max": "higher",
        "action_norm_mean": "higher",
        "action_delta_mean": "higher",
        "transition_step_mean": "higher",
        "transition_step_p90": "higher",
        "reward_mean": "lower",
        "terminated_mean": "higher",
    }


def percentile_rank(samples: np.ndarray, observed: float, direction: str) -> float:
    if direction == "higher":
        return clean_float(float((np.sum(samples >= observed) + 1.0) / (len(samples) + 1.0)))
    if direction == "lower":
        return clean_float(float((np.sum(samples <= observed) + 1.0) / (len(samples) + 1.0)))
    if direction == "either":
        centered = samples - float(np.mean(samples))
        obs = abs(observed - float(np.mean(samples)))
        return clean_float(float((np.sum(np.abs(centered) >= obs) + 1.0) / (len(samples) + 1.0)))
    raise ValueError(direction)


def hard_gap_test(
    descriptor: dict[int, float],
    hard: set[int],
    *,
    seed: int,
    direction: str,
) -> dict[str, Any]:
    eps = np.asarray(sorted(descriptor), dtype=np.int64)
    values = np.asarray([descriptor[int(ep)] for ep in eps], dtype=np.float64)
    hard_mask = np.asarray([int(ep) in hard for ep in eps], dtype=bool)
    observed = clean_float(float(np.mean(values[hard_mask]) - np.mean(values[~hard_mask])))
    rng = np.random.default_rng(seed)
    n_hard = int(np.sum(hard_mask))
    samples = np.zeros(BOOTSTRAPS, dtype=np.float64)
    all_idx = np.arange(len(eps))
    for i in range(BOOTSTRAPS):
        pick = rng.choice(all_idx, size=n_hard, replace=False)
        mask = np.zeros(len(eps), dtype=bool)
        mask[pick] = True
        samples[i] = float(np.mean(values[mask]) - np.mean(values[~mask]))
    return {
        "hard_mean": clean_float(float(np.mean(values[hard_mask]))),
        "non_hard_mean": clean_float(float(np.mean(values[~hard_mask]))),
        "hard_minus_non_hard": observed,
        "permutation_p": percentile_rank(samples, observed, direction),
        "direction": direction,
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Environment-State Descriptors",
        "",
        f"- hard episodes: `{report['hard_episode_union']}`",
        f"- strongest descriptor: `{report['summary']['strongest_descriptor']}`",
        f"- strongest p: `{report['summary']['strongest_permutation_p']:.6g}`",
        f"- descriptor hits: `{report['summary']['descriptor_hit_count']}`",
        "",
        "| descriptor | direction | hard mean | non-hard mean | gap | p |",
        "|---|---|---:|---:|---:|---:|",
    ]
    for name, row in report["descriptor_tests"].items():
        lines.append(
            f"| `{name}` | {row['direction']} | {row['hard_mean']:.6g} | {row['non_hard_mean']:.6g} | "
            f"{row['hard_minus_non_hard']:.6g} | {row['permutation_p']:.6g} |"
        )
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Diagnose hard episodes with explicit two-rooms environment-state descriptors")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--latents", default=str(DEFAULT_LATENTS))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--seed", type=int, default=9061)
    args = parser.parse_args()

    aligned = load_npz(Path(args.export))
    latents = load_npz(Path(args.latents))
    hard_episodes = read_hard_episodes(Path(args.hard_diagnostic))
    eval_rows = anchor_env_rows(aligned, latents, "eval")
    descriptors = build_episode_descriptors(eval_rows)
    directions = descriptor_directions()
    hard = set(hard_episodes)
    tests = {
        name: hard_gap_test(values, hard, seed=args.seed + idx * 19, direction=directions[name])
        for idx, (name, values) in enumerate(descriptors.items())
    }
    strongest_name = min(tests, key=lambda name: float(tests[name]["permutation_p"]))
    hits = [name for name, row in tests.items() if float(row["permutation_p"]) <= 0.10]
    verdict = (
        "Explicit two-rooms environment-state descriptors separate the recurring hard episodes at diagnostic strength; "
        "this supports environment-state or causal-geometry conditioning for the next allocation objective."
        if hits
        else "Explicit two-rooms environment-state descriptors do not separate the recurring hard episodes at the diagnostic gate; "
        "the remaining boundary requires deeper causal perturbation probes."
    )
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_environment_state_descriptors",
        "hard_episode_union": hard_episodes,
        "descriptor_tests": tests,
        "summary": {
            "strongest_descriptor": strongest_name,
            "strongest_permutation_p": tests[strongest_name]["permutation_p"],
            "descriptor_hit_count": int(len(hits)),
            "descriptor_hits": hits,
        },
        "verdict": verdict,
        "leakage_attestation": {
            "descriptor_features": "explicit two-rooms state/action fields from the source latent export: positions, room indicators, crossing flags, rewards, and action magnitudes",
            "descriptor_fit": "no descriptor is fit to hard episode ids; hard ids are used only after descriptor construction for diagnostic permutation tests",
            "targets_not_used_for_descriptor": ["option_error", "true_mv", "horizon_y", "next_target"],
            "source": str(Path(args.latents)),
        },
        "not_claimed": ["allocation closure", "deployable policy", "hard-regime training result"],
    }
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
