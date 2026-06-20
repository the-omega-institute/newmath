"""Core semantics for the CIT causal-transfer benchmark."""

from __future__ import annotations

from dataclasses import dataclass, replace
import math
import random
from statistics import mean
from typing import Any, Iterable, Mapping, Sequence

try:  # pragma: no cover - exercised through CUDA-gated tests when available.
    import torch
    from torch import nn
except ImportError:  # pragma: no cover
    torch = None
    nn = None


@dataclass(frozen=True)
class CITConfig:
    seed: int = 1726
    train_n: int = 256
    eval_n: int = 256
    q: int = 2
    hidden_dim: int = 16
    epochs: int = 120
    lr: float = 0.02
    batch_size: int = 64
    bootstrap_samples: int = 200
    ci_alpha: float = 0.05
    independent_w: bool = False
    bayes_indifferent: bool = False
    view: str = "causal"
    device: str = "cpu"


def _require_torch() -> Any:
    if torch is None or nn is None:
        raise RuntimeError("torch is required for CIT causal-transfer training")
    return torch


def _balanced_labels(index: int) -> int:
    return index % 2


def _source_row(index: int, *, q: int, rng: random.Random, independent_w: bool, bayes_indifferent: bool) -> dict[str, Any]:
    label = _balanced_labels(index)
    witness = index % q
    if independent_w or bayes_indifferent:
        action = rng.randrange(q)
        witness = rng.randrange(q)
        return {
            "w": witness,
            "action": action,
            "label": label,
            "source": "indifferent" if bayes_indifferent else "independent_w",
            "nuisance": rng.random() - 0.5,
        }
    action = witness if label == 1 else (witness + 1 + (index % max(1, q - 1))) % q
    return {
        "w": witness,
        "action": action,
        "label": label,
        "source": "causal",
        "nuisance": rng.random() - 0.5,
    }


def generate_base_dataset(config: CITConfig, *, n: int | None = None, seed_offset: int = 0) -> list[dict[str, Any]]:
    rng = random.Random(config.seed + seed_offset)
    count = int(config.train_n if n is None else n)
    return [
        _source_row(
            index,
            q=2,
            rng=rng,
            independent_w=config.independent_w,
            bayes_indifferent=config.bayes_indifferent,
        )
        for index in range(count)
    ]


def generate_dataset(config: CITConfig, *, n: int | None = None, seed_offset: int = 0) -> list[dict[str, Any]]:
    return generate_base_dataset(replace(config, q=2), n=n, seed_offset=seed_offset)


def generate_q_dataset(config: CITConfig, *, n: int | None = None, seed_offset: int = 0) -> list[dict[str, Any]]:
    if config.q < 2:
        raise ValueError("q must be at least 2")
    rng = random.Random(config.seed + seed_offset)
    count = int(config.train_n if n is None else n)
    return [
        _source_row(
            index,
            q=config.q,
            rng=rng,
            independent_w=config.independent_w,
            bayes_indifferent=config.bayes_indifferent,
        )
        for index in range(count)
    ]


def _one_hot(value: int, width: int) -> list[float]:
    return [1.0 if int(value) == index else 0.0 for index in range(width)]


def arm_view(row: Mapping[str, Any], config: CITConfig, *, view: str | None = None) -> list[float]:
    selected = config.view if view is None else view
    q = int(config.q)
    if selected == "blank" or config.independent_w or config.bayes_indifferent:
        return [0.0 for _ in range((2 * q) + 2)]
    action = int(row["action"])
    witness = int(row["w"])
    if selected == "action":
        return _one_hot(action, q) + [0.0 for _ in range(q + 2)]
    if selected == "witness":
        return [0.0 for _ in range(q)] + _one_hot(witness, q) + [0.0, float(row.get("nuisance", 0.0))]
    if selected != "causal":
        raise ValueError(f"unknown CIT arm view: {selected}")
    return (
        _one_hot(action, q)
        + _one_hot(witness, q)
        + [1.0 if action == witness else 0.0, float(row.get("nuisance", 0.0))]
    )


def to_tensors(rows: Sequence[Mapping[str, Any]], config: CITConfig, *, view: str | None = None) -> tuple[Any, Any]:
    backend = _require_torch()
    x_rows = [arm_view(row, config, view=view) for row in rows]
    y_rows = [float(row["label"]) for row in rows]
    device = backend.device(config.device)
    x_tensor = backend.tensor(x_rows, dtype=backend.float32, device=device)
    y_tensor = backend.tensor(y_rows, dtype=backend.float32, device=device).unsqueeze(1)
    return x_tensor, y_tensor


if nn is not None:

    class CITNet(nn.Module):
        """Small classifier used by the binary causal-transfer arm."""

        def __init__(self, input_dim: int, hidden_dim: int = 16) -> None:
            super().__init__()
            self.net = nn.Sequential(
                nn.Linear(input_dim, hidden_dim),
                nn.ReLU(),
                nn.Linear(hidden_dim, 1),
            )

        def forward(self, x: Any) -> Any:
            return self.net(x)


    class CITNetQ(nn.Module):
        """Small classifier used by the q-source causal-transfer arm."""

        def __init__(self, input_dim: int, hidden_dim: int = 16) -> None:
            super().__init__()
            self.net = nn.Sequential(
                nn.Linear(input_dim, hidden_dim),
                nn.ReLU(),
                nn.Linear(hidden_dim, 1),
            )

        def forward(self, x: Any) -> Any:
            return self.net(x)

else:

    class CITNet:  # pragma: no cover
        def __init__(self, *_: Any, **__: Any) -> None:
            _require_torch()


    class CITNetQ:  # pragma: no cover
        def __init__(self, *_: Any, **__: Any) -> None:
            _require_torch()


def train_model(model: Any, x_train: Any, y_train: Any, config: CITConfig) -> Any:
    backend = _require_torch()
    backend.manual_seed(config.seed)
    optimizer = backend.optim.Adam(model.parameters(), lr=config.lr)
    loss_fn = nn.BCEWithLogitsLoss()
    count = x_train.shape[0]
    batch_size = max(1, min(config.batch_size, count))
    for _epoch in range(config.epochs):
        order = backend.randperm(count, device=x_train.device)
        for start in range(0, count, batch_size):
            batch = order[start : start + batch_size]
            optimizer.zero_grad(set_to_none=True)
            loss = loss_fn(model(x_train[batch]), y_train[batch])
            loss.backward()
            optimizer.step()
    return model


def predict_probabilities(model: Any, x_eval: Any) -> list[float]:
    backend = _require_torch()
    model.eval()
    with backend.no_grad():
        probs = backend.sigmoid(model(x_eval)).squeeze(1)
    return [float(value) for value in probs.detach().cpu().tolist()]


def evaluate_probabilities(probabilities: Sequence[float], labels: Sequence[int | float]) -> dict[str, Any]:
    predictions = [1 if value >= 0.5 else 0 for value in probabilities]
    correct = [1.0 if prediction == int(label) else 0.0 for prediction, label in zip(predictions, labels)]
    return {
        "accuracy": mean(correct) if correct else 0.0,
        "correct": correct,
        "count": len(correct),
    }


def bootstrap_ci(
    values: Sequence[float],
    *,
    samples: int = 200,
    alpha: float = 0.05,
    seed: int = 0,
) -> dict[str, float]:
    if not values:
        return {"mean": 0.0, "lower": 0.0, "upper": 0.0}
    rng = random.Random(seed)
    draws = []
    count = len(values)
    for _ in range(max(1, samples)):
        draws.append(mean(values[rng.randrange(count)] for _index in range(count)))
    draws.sort()
    lower_index = max(0, min(len(draws) - 1, int(math.floor((alpha / 2.0) * len(draws)))))
    upper_index = max(0, min(len(draws) - 1, int(math.ceil((1.0 - alpha / 2.0) * len(draws))) - 1))
    return {"mean": mean(values), "lower": draws[lower_index], "upper": draws[upper_index]}


def summarize_accuracy(correct: Sequence[float], config: CITConfig) -> dict[str, Any]:
    interval = bootstrap_ci(
        correct,
        samples=config.bootstrap_samples,
        alpha=config.ci_alpha,
        seed=config.seed + 911,
    )
    return {
        "point": interval["mean"],
        "ci": {"lower": interval["lower"], "upper": interval["upper"], "alpha": config.ci_alpha},
        "n": len(correct),
    }


def analytic_bayes_2afc(config: CITConfig) -> float:
    if config.independent_w or config.bayes_indifferent or config.view in {"blank", "action", "witness"}:
        return 0.5
    return 1.0


def analytic_bayes_q(config: CITConfig) -> float:
    if config.independent_w or config.bayes_indifferent or config.view in {"blank", "action", "witness"}:
        return 0.5
    return 1.0


def bayes_posterior_2afc(row: Mapping[str, Any], config: CITConfig) -> dict[str, float]:
    if analytic_bayes_2afc(config) == 0.5:
        return {"p0": 0.5, "p1": 0.5}
    p1 = 1.0 if int(row["action"]) == int(row["w"]) else 0.0
    return {"p0": 1.0 - p1, "p1": p1}


def bayes_posterior_q(row: Mapping[str, Any], config: CITConfig) -> dict[str, float]:
    if analytic_bayes_q(config) == 0.5:
        return {"p0": 0.5, "p1": 0.5}
    p1 = 1.0 if int(row["action"]) == int(row["w"]) else 0.0
    return {"p0": 1.0 - p1, "p1": p1}


def bayes_correct_flags(rows: Iterable[Mapping[str, Any]], config: CITConfig, *, q_source: bool = False) -> list[float]:
    posterior = bayes_posterior_q if q_source else bayes_posterior_2afc
    flags = []
    for row in rows:
        probs = posterior(row, config)
        prediction = 1 if probs["p1"] >= 0.5 else 0
        flags.append(1.0 if prediction == int(row["label"]) else 0.0)
    return flags


def _train_and_score(
    config: CITConfig,
    *,
    q_source: bool,
    train_seed_offset: int,
    eval_seed_offset: int,
) -> dict[str, Any]:
    backend = _require_torch()
    backend.manual_seed(config.seed)
    generator = generate_q_dataset if q_source else generate_dataset
    train_rows = generator(config, n=config.train_n, seed_offset=train_seed_offset)
    eval_rows = generator(config, n=config.eval_n, seed_offset=eval_seed_offset)
    x_train, y_train = to_tensors(train_rows, config)
    x_eval, _y_eval = to_tensors(eval_rows, config)
    model_class = CITNetQ if q_source else CITNet
    model = model_class(input_dim=x_train.shape[1], hidden_dim=config.hidden_dim).to(config.device)
    train_model(model, x_train, y_train, config)
    probabilities = predict_probabilities(model, x_eval)
    labels = [int(row["label"]) for row in eval_rows]
    evaluation = evaluate_probabilities(probabilities, labels)
    learned = summarize_accuracy(evaluation["correct"], config)
    bayes_flags = bayes_correct_flags(eval_rows, config, q_source=q_source)
    bayes = summarize_accuracy(bayes_flags, config)
    analytic = analytic_bayes_q(config) if q_source else analytic_bayes_2afc(config)
    return {
        "config": {
            "seed": config.seed,
            "train_n": config.train_n,
            "eval_n": config.eval_n,
            "q": config.q,
            "independent_w": config.independent_w,
            "bayes_indifferent": config.bayes_indifferent,
            "view": config.view,
            "device": config.device,
        },
        "learned": learned,
        "analytic_bayes": analytic,
        "bayes_empirical": bayes,
        "probability_mean": mean(probabilities) if probabilities else 0.0,
    }


def run_arm(config: CITConfig) -> dict[str, Any]:
    return {"arm": "causal-transfer", **_train_and_score(config, q_source=False, train_seed_offset=0, eval_seed_offset=10_000)}


def run_fresh_action(config: CITConfig) -> dict[str, Any]:
    fresh = replace(config, view="causal")
    return {"arm": "fresh-action", **_train_and_score(fresh, q_source=False, train_seed_offset=1_000, eval_seed_offset=11_000)}


def run_q_arm(config: CITConfig) -> dict[str, Any]:
    q_config = replace(config, q=max(3, config.q), view="causal")
    return {"arm": "q-source", **_train_and_score(q_config, q_source=True, train_seed_offset=2_000, eval_seed_offset=12_000)}


def run_fresh_pooled(config: CITConfig) -> dict[str, Any]:
    arms = [
        run_fresh_action(config),
        run_arm(replace(config, seed=config.seed + 17)),
        run_q_arm(replace(config, seed=config.seed + 31, q=max(3, config.q))),
    ]
    points = [float(arm["learned"]["point"]) for arm in arms]
    return {
        "arm": "fresh-pooled",
        "arms": arms,
        "learned": {
            "point": mean(points) if points else 0.0,
            "min": min(points) if points else 0.0,
            "max": max(points) if points else 0.0,
        },
    }
