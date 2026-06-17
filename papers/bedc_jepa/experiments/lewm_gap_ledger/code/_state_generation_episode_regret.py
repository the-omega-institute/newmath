from __future__ import annotations

import argparse
import json
import math
import os
import random
import time
from pathlib import Path
from typing import Any

os.environ["CUBLAS_WORKSPACE_CONFIG"] = ":4096:8"

import numpy as np
import torch
import torch.nn.functional as F

import _compute_value_structured_assignment as structured
import _state_generation_episode_allocation as episode_alloc


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_episode_regret.json"
DEFAULT_MD = REPORT_DIR / "state_generation_episode_regret.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_episode_regret_predictions.npz"


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


def configure(seed: int) -> torch.device:
    os.environ["PYTHONHASHSEED"] = str(seed)
    random.seed(seed)
    np.random.seed(seed)
    torch.manual_seed(seed)
    if torch.cuda.is_available():
        torch.cuda.manual_seed_all(seed)
    torch.use_deterministic_algorithms(True)
    torch.backends.cudnn.benchmark = False
    torch.backends.cudnn.deterministic = True
    return torch.device("cuda" if torch.cuda.is_available() else "cpu")


def episode_groups(episode: np.ndarray) -> list[np.ndarray]:
    return [np.flatnonzero(episode.astype(np.int64) == int(value)).astype(np.int64) for value in np.unique(episode.astype(np.int64))]


def random_exact_budget_assignment(n: int, rng: np.random.Generator) -> np.ndarray:
    cols = np.full(n, 2, dtype=np.int64)
    if n < 2:
        return cols
    order = rng.permutation(n)
    cursor = 0
    max_pairs = n // 2
    pair_count = int(rng.integers(1, max_pairs + 1)) if max_pairs > 0 else 0
    for _ in range(pair_count):
        if cursor + 1 >= n:
            break
        a = int(order[cursor])
        b = int(order[cursor + 1])
        cursor += 2
        if float(rng.random()) < 0.5:
            low, high = (0, 4)
        else:
            low, high = (1, 3)
        if float(rng.random()) < 0.5:
            cols[a] = low
            cols[b] = high
        else:
            cols[a] = high
            cols[b] = low
    return cols


def static_competitors(split: dict[str, np.ndarray], oracle: np.ndarray, *, seed: int, per_episode: int) -> list[dict[str, Any]]:
    rng = np.random.default_rng(seed)
    out: list[dict[str, Any]] = []
    for idxs in episode_groups(split["episode"]):
        idxs = idxs.astype(np.int64)
        oracle_cols = oracle[idxs].astype(np.int64)
        oracle_error = float(np.sum(split["option_error"][idxs, oracle_cols]))
        competitors: list[dict[str, Any]] = []
        uniform = np.full(len(idxs), 2, dtype=np.int64)
        choices = [uniform]
        for _ in range(per_episode):
            choices.append(random_exact_budget_assignment(len(idxs), rng))
        seen: set[tuple[int, ...]] = set()
        for cols in choices:
            key = tuple(int(x) for x in cols)
            if key in seen or np.array_equal(cols, oracle_cols):
                continue
            seen.add(key)
            comp_error = float(np.sum(split["option_error"][idxs, cols]))
            regret = max(0.0, comp_error - oracle_error) / max(1, len(idxs))
            if regret <= 1.0e-10:
                continue
            competitors.append({"cols": cols.astype(np.int64), "regret": clean_float(regret)})
        out.append({"idxs": idxs, "oracle_cols": oracle_cols, "competitors": competitors})
    return out


def structured_margin_loss(
    score: torch.Tensor,
    groups: list[dict[str, Any]],
    *,
    device: torch.device,
    hard_choice: np.ndarray | None,
    option_error: np.ndarray,
) -> torch.Tensor:
    losses: list[torch.Tensor] = []
    for group in groups:
        idxs_np = group["idxs"]
        idxs = torch.as_tensor(idxs_np, dtype=torch.long, device=device)
        oracle_cols_np = group["oracle_cols"]
        oracle_cols = torch.as_tensor(oracle_cols_np, dtype=torch.long, device=device)
        oracle_score = score[idxs, oracle_cols].sum() / max(1, len(idxs_np))
        for comp in group["competitors"]:
            comp_cols = torch.as_tensor(comp["cols"], dtype=torch.long, device=device)
            comp_score = score[idxs, comp_cols].sum() / max(1, len(idxs_np))
            margin = torch.tensor(float(comp["regret"]), dtype=score.dtype, device=device)
            losses.append(F.softplus(oracle_score - comp_score + margin))
        if hard_choice is not None:
            hard_cols_np = hard_choice[idxs_np].astype(np.int64)
            if not np.array_equal(hard_cols_np, oracle_cols_np):
                oracle_error = float(np.sum(option_error[idxs_np, oracle_cols_np]))
                hard_error = float(np.sum(option_error[idxs_np, hard_cols_np]))
                regret = max(0.0, hard_error - oracle_error) / max(1, len(idxs_np))
                if regret > 1.0e-10:
                    hard_cols = torch.as_tensor(hard_cols_np, dtype=torch.long, device=device)
                    hard_score = score[idxs, hard_cols].sum() / max(1, len(idxs_np))
                    margin = torch.tensor(float(regret), dtype=score.dtype, device=device)
                    losses.append(F.softplus(oracle_score - hard_score + margin))
    if not losses:
        return score.sum() * 0.0
    return torch.stack(losses).mean()


def train_model(
    train_x: np.ndarray,
    train_split: dict[str, np.ndarray],
    train_oracle: np.ndarray,
    cal_x: np.ndarray,
    cal_split: dict[str, np.ndarray],
    *,
    device: torch.device,
    seed: int,
    hidden: int,
    depth: int,
    epochs: int,
    lr: float,
    competitor_count: int,
) -> tuple[episode_alloc.EpisodeAllocationNet, dict[str, Any]]:
    model = episode_alloc.EpisodeAllocationNet(train_x.shape[1], structured.DEPTHS.shape[0], hidden, depth).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=1.0e-4)
    x_t = torch.from_numpy(train_x.astype(np.float32)).to(device)
    target_t = torch.from_numpy(episode_alloc.centered_errors(train_split["option_error"]).astype(np.float32)).to(device)
    oracle_t = torch.from_numpy(train_oracle.astype(np.int64)).to(device)
    depths_t = torch.from_numpy(structured.DEPTHS.astype(np.float32)).to(device)
    groups = static_competitors(train_split, train_oracle, seed=seed + 3100, per_episode=competitor_count)
    best_state = None
    best_key = (float("inf"), float("inf"))
    best: dict[str, Any] = {}
    history: list[dict[str, float]] = []
    for epoch in range(epochs):
        model.train()
        score = model(x_t)
        centered_score = score - torch.mean(score, dim=1, keepdim=True)
        with torch.no_grad():
            hard_choice = structured.exact_budget_choice(
                train_split["episode"],
                score.detach().cpu().numpy().astype(np.float64),
                structured.DEPTHS,
            )
        regret_loss = structured_margin_loss(
            score,
            groups,
            device=device,
            hard_choice=hard_choice,
            option_error=train_split["option_error"],
        )
        ce = F.cross_entropy(-score, oracle_t)
        rank = episode_alloc.pairwise_loss(centered_score, target_t)
        reg = F.smooth_l1_loss(centered_score, target_t)
        balance = episode_alloc.depth_balance_loss(score, oracle_t, depths_t)
        loss = 0.45 * regret_loss + 0.25 * ce + 0.15 * rank + 0.10 * balance + 0.05 * reg
        opt.zero_grad(set_to_none=True)
        loss.backward()
        torch.nn.utils.clip_grad_norm_(model.parameters(), 5.0)
        opt.step()
        cal_score = episode_alloc.predict(model, cal_x, device, 256)
        cal_eval = episode_alloc.evaluate(cal_split, cal_score, seed=seed + 3800 + epoch)
        delta = cal_eval["allocation_delta"]
        key = (float(delta["high"]), float(delta["observed"]))
        history.append(
            {
                "epoch": float(epoch + 1),
                "train_loss": clean_float(float(loss.detach().cpu())),
                "regret_loss": clean_float(float(regret_loss.detach().cpu())),
                "cal_delta_observed": clean_float(float(delta["observed"])),
                "cal_delta_high": clean_float(float(delta["high"])),
                "cal_oracle_match": clean_float(float(cal_eval["oracle_match"])),
                "cal_spearman": clean_float(float(cal_eval["score_error_spearman"])),
            }
        )
        if key < best_key:
            best_key = key
            best = {"epoch": int(epoch + 1), "calibration": cal_eval, "selection_key": list(key)}
            best_state = {name: value.detach().cpu().clone() for name, value in model.state_dict().items()}
    if best_state is not None:
        model.load_state_dict(best_state)
    competitor_total = int(sum(len(group["competitors"]) for group in groups))
    return model, {
        "selection_rule": "minimize calibration exact-budget allocation_delta CI high, then observed delta",
        "best": best,
        "history_first": history[0] if history else {},
        "history_last": history[-1] if history else {},
        "params_count": int(sum(p.numel() for p in model.parameters())),
        "static_competitor_count": competitor_total,
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    rows = report["eval"]
    lines = [
        "# State-Generation Episode Regret",
        "",
        f"- device: `{report['device']}`",
        f"- selected epoch: `{report['selection']['best']['epoch']}`",
        "",
        "| scorer | allocation delta | rho | oracle match |",
        "|---|---:|---:|---:|",
    ]
    for name in ["episode_regret", "episode_allocation", "episode_dual_price", "allocation_native", "oracle_true_error"]:
        row = rows[name]
        d = row["allocation_delta"]
        lines.append(
            f"| `{name}` | {d['observed']:.6g} [{d['low']:.6g}, {d['high']:.6g}] | "
            f"{row['score_error_spearman']:.6g} | {row.get('oracle_match', 0.0):.6g} |"
        )
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Train a direct episode-regret allocation objective")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--allocation-native", default=str(REPORT_DIR / "state_generation_allocation_native_predictions.npz"))
    parser.add_argument("--episode-allocation", default=str(REPORT_DIR / "state_generation_episode_allocation_predictions.npz"))
    parser.add_argument("--episode-dual-price", default=str(REPORT_DIR / "state_generation_episode_dual_price_predictions.npz"))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=881)
    parser.add_argument("--epochs", type=int, default=180)
    parser.add_argument("--hidden", type=int, default=256)
    parser.add_argument("--depth", type=int, default=2)
    parser.add_argument("--lr", type=float, default=3.0e-4)
    parser.add_argument("--competitors", type=int, default=12)
    args = parser.parse_args()
    start_time = time.time()
    device = configure(int(args.seed))
    with np.load(Path(args.export), allow_pickle=False) as archive:
        data = {key: archive[key] for key in archive.files}
    train = episode_alloc.load_split(data, "train")
    cal = episode_alloc.load_split(data, "calibration")
    eval_split = episode_alloc.load_split(data, "eval")
    option_depths = data["option_depths"].astype(np.int64)
    if not np.array_equal(option_depths, structured.DEPTHS.astype(np.int64)):
        raise ValueError(f"option depths mismatch: {option_depths} vs {structured.DEPTHS}")
    mean, scale = episode_alloc.standardizer(train["x"])
    train_x = episode_alloc.apply_standardizer(train["x"], mean, scale)
    cal_x = episode_alloc.apply_standardizer(cal["x"], mean, scale)
    eval_x = episode_alloc.apply_standardizer(eval_split["x"], mean, scale)
    train_oracle = episode_alloc.oracle_choice(train)
    eval_oracle = episode_alloc.oracle_choice(eval_split)
    model, selection = train_model(
        train_x,
        train,
        train_oracle,
        cal_x,
        cal,
        device=device,
        seed=int(args.seed),
        hidden=int(args.hidden),
        depth=int(args.depth),
        epochs=int(args.epochs),
        lr=float(args.lr),
        competitor_count=int(args.competitors),
    )
    eval_score = episode_alloc.predict(model, eval_x, device, 256)
    with np.load(Path(args.allocation_native), allow_pickle=False) as native:
        allocation_native_score = native["allocation_native_score"].astype(np.float64)
    with np.load(Path(args.episode_allocation), allow_pickle=False) as episode_pred:
        episode_score = episode_pred["episode_allocation_score"].astype(np.float64)
    with np.load(Path(args.episode_dual_price), allow_pickle=False) as dual_pred:
        dual_score = dual_pred["dual_price_score"].astype(np.float64)
    rows = {
        "episode_regret": episode_alloc.evaluate(eval_split, eval_score, seed=int(args.seed) + 1201),
        "episode_allocation": episode_alloc.evaluate(eval_split, episode_score, seed=int(args.seed) + 1201),
        "episode_dual_price": episode_alloc.evaluate(eval_split, dual_score, seed=int(args.seed) + 1201),
        "allocation_native": episode_alloc.evaluate(eval_split, allocation_native_score, seed=int(args.seed) + 1201),
        "oracle_true_error": episode_alloc.evaluate(eval_split, eval_split["option_error"], seed=int(args.seed) + 1201),
    }
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_episode_regret",
        "device": str(device),
        "config": {
            "epochs": int(args.epochs),
            "hidden": int(args.hidden),
            "depth": int(args.depth),
            "lr": float(args.lr),
            "competitors_per_episode": int(args.competitors),
            "loss": "0.45*structured_assignment_regret + 0.25*oracle_choice_ce + 0.15*option_order + 0.10*expected_depth + 0.05*centered_error",
        },
        "counts": {
            "train": int(len(train_x)),
            "calibration": int(len(cal_x)),
            "eval": int(len(eval_x)),
            "eval_episodes": int(len(np.unique(eval_split["episode"]))),
        },
        "selection": selection,
        "eval": rows,
        "diagnosis": {
            "allocation_closed": bool(float(rows["episode_regret"]["allocation_delta"]["high"]) < 0.0),
            "beats_episode_objective_observed": bool(float(rows["episode_regret"]["allocation_delta"]["observed"]) < float(rows["episode_allocation"]["allocation_delta"]["observed"])),
            "beats_episode_objective_ci_high": bool(float(rows["episode_regret"]["allocation_delta"]["high"]) < float(rows["episode_allocation"]["allocation_delta"]["high"])),
            "beats_dual_price_observed": bool(float(rows["episode_regret"]["allocation_delta"]["observed"]) < float(rows["episode_dual_price"]["allocation_delta"]["observed"])),
            "beats_dual_price_ci_high": bool(float(rows["episode_regret"]["allocation_delta"]["high"]) < float(rows["episode_dual_price"]["allocation_delta"]["high"])),
            "beats_allocation_native_observed": bool(float(rows["episode_regret"]["allocation_delta"]["observed"]) < float(rows["allocation_native"]["allocation_delta"]["observed"])),
            "beats_allocation_native_ci_high": bool(float(rows["episode_regret"]["allocation_delta"]["high"]) < float(rows["allocation_native"]["allocation_delta"]["high"])),
            "oracle_closed": bool(float(rows["oracle_true_error"]["allocation_delta"]["high"]) < 0.0),
        },
        "leakage_attestation": {
            "features": "aligned export x only",
            "targets": "train option_error is converted to exact-budget oracle assignments and same-budget competitors; eval option_error used only after score generation for metrics",
            "selection": "calibration exact-budget allocation_delta CI high, then observed delta",
            "slurm_or_ssh": "not used",
        },
        "not_claimed": ["allocation closure", "deployable policy", "complete BEDC-native world model"],
        "wall_time_sec": clean_float(time.time() - start_time),
    }
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    chosen = structured.exact_budget_choice(eval_split["episode"], eval_score, structured.DEPTHS)
    np.savez_compressed(
        Path(args.out),
        episode=eval_split["episode"].astype(np.int64),
        anchor_ep_t0=eval_split["anchor_ep_t0"].astype(np.int64),
        option_depths=option_depths.astype(np.int64),
        option_error=eval_split["option_error"].astype(np.float64),
        episode_regret_score=eval_score.astype(np.float64),
        episode_allocation_score=episode_score.astype(np.float64),
        dual_price_score=dual_score.astype(np.float64),
        allocation_native_score=allocation_native_score.astype(np.float64),
        oracle_choice=eval_oracle.astype(np.int64),
        chosen_col=chosen.astype(np.int64),
        chosen_depth=option_depths[chosen].astype(np.int64),
    )
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
