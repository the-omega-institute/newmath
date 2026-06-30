#!/usr/bin/env python3
"""Golden/Fibonacci impossibility for biological translation kernels.

The experiment is a correspondence-negative certificate.  It numerically
corroborates the structural obstruction:

* A biological decoding transition matrix is column-substochastic, hence its
  spectral radius is at most one.
* A CTMC translation generator has eigenvalues in the closed left half-plane.
* The polynomial x^2 - x - 1 has the positive root phi > 1, so it cannot divide
  the characteristic polynomial of either admissible biological operator.

The other root psi is inside the unit disk.  The obstruction is therefore not
"the polynomial has no unit-disk root"; it is that divisibility requires the
positive golden root phi, which stochastic biology cannot supply.
"""
from __future__ import annotations

import json
import math
import random
import sys

try:
    import numpy as np
except ModuleNotFoundError:  # pragma: no cover - exercised only in minimal Python environments.
    np = None  # type: ignore[assignment]


EXPERIMENT_ID = "translation_kernel_golden_impossibility"
CLAIM_ID = "bridge.translation_kernel.golden_fibonacci_impossibility"
RNG_SEED = 20260621
DIMENSIONS = tuple(range(2, 13))
SAMPLES_PER_DIMENSION = 250
TOL = 1e-9
POWER_ITERATIONS = 160


def emit(status: str, **fields: object) -> None:
    payload = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
    }
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False))
    if status in ("certified", "coincidence"):
        raise SystemExit(0)
    if status == "refuted":
        raise SystemExit(2)
    raise SystemExit(3)


def golden_polynomial_scalar(value: complex) -> complex:
    return value * value - value - 1.0


def golden_polynomial(values: np.ndarray) -> np.ndarray:  # type: ignore[name-defined]
    return values * values - values - 1.0


def spectral_radius(matrix: np.ndarray) -> float:  # type: ignore[name-defined]
    if np is None:
        raise RuntimeError("numpy spectral radius requested without numpy")
    return float(np.max(np.abs(np.linalg.eigvals(matrix))))


def random_column_substochastic(
    rng: np.random.Generator, dimension: int  # type: ignore[name-defined]
) -> np.ndarray:  # type: ignore[name-defined]
    if np is None:
        raise RuntimeError("numpy matrix requested without numpy")
    matrix = rng.random((dimension, dimension))
    column_sums = matrix.sum(axis=0)
    targets = rng.random(dimension)
    return matrix * (targets / column_sums)


def random_ctmc_generator(
    rng: np.random.Generator, dimension: int  # type: ignore[name-defined]
) -> np.ndarray:  # type: ignore[name-defined]
    if np is None:
        raise RuntimeError("numpy matrix requested without numpy")
    generator = rng.random((dimension, dimension))
    np.fill_diagonal(generator, 0.0)
    column_sums = generator.sum(axis=0)
    np.fill_diagonal(generator, -column_sums)
    return generator


def unit_circle_minimum(samples: int = 20000) -> float:
    if np is None:
        return min(
            abs(golden_polynomial_scalar(complex(math.cos(theta), math.sin(theta))))
            for theta in (
                2.0 * math.pi * index / samples for index in range(samples)
            )
        )
    theta = np.linspace(0.0, 2.0 * math.pi, samples, endpoint=False)
    z = np.exp(1j * theta)
    return float(np.min(np.abs(golden_polynomial(z))))


def random_column_substochastic_py(
    rng: random.Random, dimension: int
) -> list[list[float]]:
    matrix = [[rng.random() for _ in range(dimension)] for _ in range(dimension)]
    targets = [rng.random() for _ in range(dimension)]
    for col in range(dimension):
        column_sum = sum(matrix[row][col] for row in range(dimension))
        scale = targets[col] / column_sum
        for row in range(dimension):
            matrix[row][col] *= scale
    return matrix


def random_ctmc_generator_py(rng: random.Random, dimension: int) -> list[list[float]]:
    generator = [[rng.random() for _ in range(dimension)] for _ in range(dimension)]
    for index in range(dimension):
        generator[index][index] = 0.0
    for col in range(dimension):
        column_sum = sum(generator[row][col] for row in range(dimension))
        generator[col][col] = -column_sum
    return generator


def column_sums_py(matrix: list[list[float]]) -> list[float]:
    return [sum(matrix[row][col] for row in range(len(matrix))) for col in range(len(matrix))]


def matvec_py(matrix: list[list[float]], vector: list[float]) -> list[float]:
    return [
        sum(matrix[row][col] * vector[col] for col in range(len(vector)))
        for row in range(len(matrix))
    ]


def perron_radius_estimate_py(matrix: list[list[float]]) -> float:
    dimension = len(matrix)
    vector = [1.0 / dimension for _ in range(dimension)]
    estimate = 0.0
    for _ in range(POWER_ITERATIONS):
        nxt = matvec_py(matrix, vector)
        total = sum(nxt)
        if total <= 0.0:
            return 0.0
        estimate = total / sum(vector)
        vector = [value / total for value in nxt]
    return estimate


def ctmc_gershgorin_right_edge_py(generator: list[list[float]]) -> float:
    right_edges = []
    for col in range(len(generator)):
        center = generator[col][col]
        radius = sum(
            abs(generator[row][col])
            for row in range(len(generator))
            if row != col
        )
        right_edges.append(center + radius)
    return max(right_edges)


def build_certificate() -> dict[str, object]:
    return {
        "verdict": "correspondence_negative",
        "structural_argument": [
            (
                "A biologically legitimate discrete decoding kernel is a "
                "nonnegative column-substochastic matrix P."
            ),
            (
                "For such P, the induced one-norm is at most one, hence every "
                "eigenvalue lambda satisfies |lambda| <= rho(P) <= 1."
            ),
            (
                "If x^2 - x - 1 divided the characteristic polynomial of P, "
                "then the positive golden root phi would be an eigenvalue, "
                "contradicting rho(P) <= 1 < phi."
            ),
            (
                "A CTMC generator Q with nonnegative off-diagonal rates and "
                "zero column sums generates a stochastic semigroup; its "
                "eigenvalues have non-positive real part, so phi cannot be a "
                "generator eigenvalue."
            ),
            (
                "The polynomial x^2 - x - 1 is unit-free, while generator "
                "eigenvalues carry inverse-time units; exact polynomial "
                "division is not a biological invariant of Q."
            ),
            (
                "The companion matrix [[1, 1], [1, 0]] realizes the golden "
                "recurrence only as an unnormalized two-state path-counting "
                "quotient with a no-consecutive-state rule, which is an "
                "imposed Window6 automaton rather than a decoding kernel."
            ),
        ],
    }


def emit_refutation(
    *,
    checks: list[dict[str, object]],
    max_substochastic_spectral_radius: float,
    companion_spectral_radius: float,
    max_ctmc_eig_real_part: float,
    unit_circle_min_modulus: float,
    substochastic_samples: int,
    ctmc_samples: int,
    eigensolver: str,
) -> None:
    phi = (1.0 + math.sqrt(5.0)) / 2.0
    emit(
        "refuted",
        checks=checks,
        certificate=build_certificate(),
        max_substochastic_spectral_radius=max_substochastic_spectral_radius,
        phi=phi,
        companion_spectral_radius=companion_spectral_radius,
        max_ctmc_eig_real_part=max_ctmc_eig_real_part,
        poly_min_modulus_in_unit_disk=0.0,
        poly_min_modulus_on_unit_circle=unit_circle_min_modulus,
        substochastic_samples=substochastic_samples,
        ctmc_samples=ctmc_samples,
        rng_seed=RNG_SEED,
        eigensolver=eigensolver,
        reason=(
            "any biological (sub)stochastic translation operator has spectral "
            "radius <= 1 < phi, and any CTMC generator has eigenvalues with "
            "non-positive real part; x^2-x-1 cannot divide their "
            "characteristic polynomial because divisibility would require the "
            "forbidden root phi; realizing it needs an unnormalized 2-state "
            "no-adjacent counting quotient biology does not supply"
        ),
    )


def main_numpy() -> None:
    if np is None:
        raise RuntimeError("numpy path requested without numpy")
    rng = np.random.default_rng(RNG_SEED)
    phi = (1.0 + math.sqrt(5.0)) / 2.0
    psi = (1.0 - math.sqrt(5.0)) / 2.0
    companion = np.array([[1.0, 1.0], [1.0, 0.0]])
    companion_eigenvalues = np.linalg.eigvals(companion)
    companion_radius = spectral_radius(companion)

    max_substochastic_radius = 0.0
    max_column_sum = 0.0
    min_random_poly_modulus = float("inf")
    min_random_distance_to_phi = float("inf")
    substochastic_samples = 0
    substochastic_violations: list[dict[str, object]] = []

    for dimension in DIMENSIONS:
        for _ in range(SAMPLES_PER_DIMENSION):
            matrix = random_column_substochastic(rng, dimension)
            column_sums = matrix.sum(axis=0)
            eigvals = np.linalg.eigvals(matrix)
            radius = float(np.max(np.abs(eigvals)))
            max_substochastic_radius = max(max_substochastic_radius, radius)
            max_column_sum = max(max_column_sum, float(np.max(column_sums)))
            min_random_poly_modulus = min(
                min_random_poly_modulus,
                float(np.min(np.abs(golden_polynomial(eigvals)))),
            )
            min_random_distance_to_phi = min(
                min_random_distance_to_phi,
                float(np.min(np.abs(eigvals - phi))),
            )
            substochastic_samples += 1
            if radius > 1.0 + TOL:
                substochastic_violations.append(
                    {"dimension": dimension, "spectral_radius": radius}
                )

    max_ctmc_eig_real_part = -float("inf")
    max_ctmc_column_sum_abs = 0.0
    min_ctmc_offdiag = float("inf")
    ctmc_samples = 0
    ctmc_violations: list[dict[str, object]] = []

    for dimension in DIMENSIONS:
        for _ in range(SAMPLES_PER_DIMENSION):
            generator = random_ctmc_generator(rng, dimension)
            eigvals = np.linalg.eigvals(generator)
            max_real = float(np.max(eigvals.real))
            offdiag = generator.copy()
            np.fill_diagonal(offdiag, np.inf)
            min_ctmc_offdiag = min(min_ctmc_offdiag, float(np.min(offdiag)))
            max_ctmc_eig_real_part = max(max_ctmc_eig_real_part, max_real)
            max_ctmc_column_sum_abs = max(
                max_ctmc_column_sum_abs,
                float(np.max(np.abs(generator.sum(axis=0)))),
            )
            ctmc_samples += 1
            if max_real > TOL:
                ctmc_violations.append(
                    {"dimension": dimension, "max_eigenvalue_real_part": max_real}
                )

    unit_circle_min_modulus = unit_circle_minimum()
    poly_at_origin_modulus = abs(0.0 * 0.0 - 0.0 - 1.0)
    poly_at_phi = phi * phi - phi - 1.0
    poly_at_psi = psi * psi - psi - 1.0

    checks = [
        {
            "name": "random_column_substochastic_spectral_radius_bound",
            "passed": not substochastic_violations
            and max_substochastic_radius <= 1.0 + TOL,
            "samples": substochastic_samples,
            "dimensions": list(DIMENSIONS),
            "rng_seed": RNG_SEED,
            "max_observed_spectral_radius": max_substochastic_radius,
            "max_observed_column_sum": max_column_sum,
            "tolerance": TOL,
        },
        {
            "name": "golden_companion_has_phi_radius",
            "passed": companion_radius > 1.0 and phi > 1.0,
            "matrix": [[1.0, 1.0], [1.0, 0.0]],
            "eigenvalues": [
                {"real": float(value.real), "imag": float(value.imag)}
                for value in companion_eigenvalues
            ],
            "spectral_radius": companion_radius,
            "phi": phi,
        },
        {
            "name": "random_ctmc_generator_left_half_plane",
            "passed": not ctmc_violations and max_ctmc_eig_real_part <= TOL,
            "samples": ctmc_samples,
            "dimensions": list(DIMENSIONS),
            "rng_seed": RNG_SEED,
            "max_observed_eigenvalue_real_part": max_ctmc_eig_real_part,
            "max_column_sum_abs": max_ctmc_column_sum_abs,
            "min_offdiagonal_rate": min_ctmc_offdiag,
            "tolerance": TOL,
        },
        {
            "name": "golden_polynomial_root_geometry",
            "passed": phi > 1.0 and abs(psi) < 1.0,
            "phi": phi,
            "psi": psi,
            "poly_at_phi_abs": abs(poly_at_phi),
            "poly_at_psi_abs": abs(poly_at_psi),
            "poly_min_modulus_in_closed_unit_disk": 0.0,
            "poly_min_modulus_on_unit_circle": unit_circle_min_modulus,
            "poly_at_origin_modulus": poly_at_origin_modulus,
            "note": (
                "psi lies inside the unit disk, so the closed-disk minimum is "
                "zero; characteristic-polynomial divisibility is impossible "
                "because it would also require phi > 1."
            ),
        },
        {
            "name": "random_substochastic_eigenvalues_do_not_approach_phi",
            "passed": min_random_distance_to_phi >= (phi - 1.0) - 5e-8,
            "min_random_distance_to_phi": min_random_distance_to_phi,
            "theoretical_distance_lower_bound_from_unit_disk": phi - 1.0,
            "min_random_abs_poly_value": min_random_poly_modulus,
            "note": (
                "A substochastic eigenvalue may lie near psi in principle; the "
                "forbidden eigenvalue for divisibility is phi."
            ),
        },
    ]

    all_checks_pass = all(bool(check["passed"]) for check in checks)
    if not all_checks_pass:
        emit(
            "needs_derivation",
            checks=checks,
            reason="numeric corroboration failed; structural certificate not emitted",
        )

    emit_refutation(
        checks=checks,
        max_substochastic_spectral_radius=max_substochastic_radius,
        companion_spectral_radius=companion_radius,
        max_ctmc_eig_real_part=max_ctmc_eig_real_part,
        substochastic_samples=substochastic_samples,
        ctmc_samples=ctmc_samples,
        unit_circle_min_modulus=unit_circle_min_modulus,
        eigensolver="numpy.linalg.eigvals",
    )


def main_fallback() -> None:
    rng = random.Random(RNG_SEED)
    phi = (1.0 + math.sqrt(5.0)) / 2.0
    psi = (1.0 - math.sqrt(5.0)) / 2.0
    companion_radius = phi
    companion_eigenvalues = (phi, psi)

    max_substochastic_radius_estimate = 0.0
    max_substochastic_radius_bound = 0.0
    max_column_sum = 0.0
    substochastic_samples = 0
    substochastic_violations: list[dict[str, object]] = []

    for dimension in DIMENSIONS:
        for _ in range(SAMPLES_PER_DIMENSION):
            matrix = random_column_substochastic_py(rng, dimension)
            sums = column_sums_py(matrix)
            bound = max(sums)
            estimate = perron_radius_estimate_py(matrix)
            max_substochastic_radius_bound = max(max_substochastic_radius_bound, bound)
            max_substochastic_radius_estimate = max(
                max_substochastic_radius_estimate, estimate
            )
            max_column_sum = max(max_column_sum, bound)
            substochastic_samples += 1
            if bound > 1.0 + TOL or estimate > 1.0 + TOL:
                substochastic_violations.append(
                    {
                        "dimension": dimension,
                        "spectral_radius_upper_bound": bound,
                        "perron_radius_estimate": estimate,
                    }
                )

    max_ctmc_eig_real_part_bound = -float("inf")
    max_ctmc_column_sum_abs = 0.0
    min_ctmc_offdiag = float("inf")
    ctmc_samples = 0
    ctmc_violations: list[dict[str, object]] = []

    for dimension in DIMENSIONS:
        for _ in range(SAMPLES_PER_DIMENSION):
            generator = random_ctmc_generator_py(rng, dimension)
            right_edge = ctmc_gershgorin_right_edge_py(generator)
            max_ctmc_eig_real_part_bound = max(
                max_ctmc_eig_real_part_bound, right_edge
            )
            max_ctmc_column_sum_abs = max(
                max_ctmc_column_sum_abs,
                max(abs(value) for value in column_sums_py(generator)),
            )
            min_ctmc_offdiag = min(
                min_ctmc_offdiag,
                min(
                    generator[row][col]
                    for row in range(dimension)
                    for col in range(dimension)
                    if row != col
                ),
            )
            ctmc_samples += 1
            if right_edge > TOL:
                ctmc_violations.append(
                    {"dimension": dimension, "gershgorin_right_edge": right_edge}
                )

    unit_circle_min_modulus = unit_circle_minimum()
    poly_at_origin_modulus = abs(golden_polynomial_scalar(0.0))
    poly_at_phi = golden_polynomial_scalar(phi)
    poly_at_psi = golden_polynomial_scalar(psi)
    min_random_distance_to_phi = phi - max_substochastic_radius_bound

    checks = [
        {
            "name": "random_column_substochastic_spectral_radius_bound",
            "passed": not substochastic_violations
            and max_substochastic_radius_bound <= 1.0 + TOL,
            "samples": substochastic_samples,
            "dimensions": list(DIMENSIONS),
            "rng_seed": RNG_SEED,
            "max_observed_spectral_radius_upper_bound": max_substochastic_radius_bound,
            "max_observed_perron_radius_estimate": max_substochastic_radius_estimate,
            "max_observed_column_sum": max_column_sum,
            "tolerance": TOL,
            "note": (
                "numpy is unavailable in this Python environment, so the "
                "fallback reports the induced one-norm upper bound and a "
                "Perron power-iteration estimate for the positive random "
                "matrices."
            ),
        },
        {
            "name": "golden_companion_has_phi_radius",
            "passed": companion_radius > 1.0 and phi > 1.0,
            "matrix": [[1.0, 1.0], [1.0, 0.0]],
            "eigenvalues": [
                {"real": float(value), "imag": 0.0}
                for value in companion_eigenvalues
            ],
            "spectral_radius": companion_radius,
            "phi": phi,
        },
        {
            "name": "random_ctmc_generator_left_half_plane",
            "passed": not ctmc_violations and max_ctmc_eig_real_part_bound <= TOL,
            "samples": ctmc_samples,
            "dimensions": list(DIMENSIONS),
            "rng_seed": RNG_SEED,
            "max_eigenvalue_real_part_upper_bound": max_ctmc_eig_real_part_bound,
            "max_column_sum_abs": max_ctmc_column_sum_abs,
            "min_offdiagonal_rate": min_ctmc_offdiag,
            "tolerance": TOL,
            "note": (
                "Column Gershgorin disks have centers -sum(offdiag column) "
                "and radii sum(offdiag column), so their right edge is 0."
            ),
        },
        {
            "name": "golden_polynomial_root_geometry",
            "passed": phi > 1.0 and abs(psi) < 1.0,
            "phi": phi,
            "psi": psi,
            "poly_at_phi_abs": abs(poly_at_phi),
            "poly_at_psi_abs": abs(poly_at_psi),
            "poly_min_modulus_in_closed_unit_disk": 0.0,
            "poly_min_modulus_on_unit_circle": unit_circle_min_modulus,
            "poly_at_origin_modulus": poly_at_origin_modulus,
            "note": (
                "psi lies inside the unit disk, so the closed-disk minimum is "
                "zero; characteristic-polynomial divisibility is impossible "
                "because it would also require phi > 1."
            ),
        },
        {
            "name": "random_substochastic_eigenvalues_do_not_approach_phi",
            "passed": min_random_distance_to_phi >= (phi - 1.0) - 5e-8,
            "minimum_certified_distance_to_phi": min_random_distance_to_phi,
            "theoretical_distance_lower_bound_from_unit_disk": phi - 1.0,
            "note": (
                "Every eigenvalue of every sampled substochastic matrix lies "
                "in |z| <= max column sum <= 1, so none can approach phi."
            ),
        },
    ]

    if not all(bool(check["passed"]) for check in checks):
        emit(
            "needs_derivation",
            checks=checks,
            reason="numeric corroboration failed; structural certificate not emitted",
        )

    emit_refutation(
        checks=checks,
        max_substochastic_spectral_radius=max_substochastic_radius_bound,
        companion_spectral_radius=companion_radius,
        max_ctmc_eig_real_part=max_ctmc_eig_real_part_bound,
        substochastic_samples=substochastic_samples,
        ctmc_samples=ctmc_samples,
        unit_circle_min_modulus=unit_circle_min_modulus,
        eigensolver="stdlib_structural_bounds",
    )


def main() -> None:
    if np is None:
        main_fallback()
    else:
        main_numpy()


if __name__ == "__main__":
    main()
