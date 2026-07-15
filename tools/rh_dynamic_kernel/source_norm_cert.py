#!/usr/bin/env python3
"""
Exact finite source-norm / Gram certificate checker for the dynamic RH route.

The previous mirror-packet checker certifies the finite negative-direction step.
This module owns the next algebraic front-end:

    finite prime/Gamma Gram entries B_ij
        + exact square-norm certificate B = sum_k w_k v_k v_k^T, w_k >= 0
        => c^T B c = sum_k w_k (v_k . c)^2 >= 0.

It is intentionally finite and exact.  It can either consume a square-norm
certificate or construct one by exact rational LDL^T elimination when the input
matrix admits that certificate without pivoting.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from fractions import Fraction
from typing import Sequence


def Q(x: str | int | Fraction) -> Fraction:
    if isinstance(x, Fraction):
        return x
    if isinstance(x, int):
        return Fraction(x, 1)
    return Fraction(x)


def qstr(x: Fraction) -> str:
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def parse_matrix_json(text: str) -> list[list[Fraction]]:
    raw = json.loads(text)
    if not isinstance(raw, list) or not raw:
        raise ValueError("matrix must be a nonempty JSON list of rows")
    n = len(raw)
    matrix: list[list[Fraction]] = []
    for row in raw:
        if not isinstance(row, list) or len(row) != n:
            raise ValueError("matrix must be square")
        matrix.append([Q(x) for x in row])
    return matrix


def assert_symmetric(B: Sequence[Sequence[Fraction]]) -> None:
    n = len(B)
    for i in range(n):
        for j in range(n):
            if B[i][j] != B[j][i]:
                raise ValueError(f"matrix is not symmetric at ({i},{j})")


@dataclass(frozen=True)
class SourceNormTerm:
    weight: Fraction
    vector: tuple[Fraction, ...]
    label: str = "source-square"

    def entry(self, i: int, j: int) -> Fraction:
        return self.weight * self.vector[i] * self.vector[j]

    def value_on_coefficients(self, coeffs: Sequence[Fraction]) -> Fraction:
        dot = sum(v * c for v, c in zip(self.vector, coeffs))
        return self.weight * dot * dot

    def to_json(self) -> dict[str, object]:
        return {
            "label": self.label,
            "weight": qstr(self.weight),
            "vector": [qstr(x) for x in self.vector],
        }


@dataclass(frozen=True)
class SourceNormCertificate:
    matrix: tuple[tuple[Fraction, ...], ...]
    terms: tuple[SourceNormTerm, ...]

    @property
    def size(self) -> int:
        return len(self.matrix)

    def reconstructed_entry(self, i: int, j: int) -> Fraction:
        return sum(term.entry(i, j) for term in self.terms)

    def reconstructed_matrix(self) -> tuple[tuple[Fraction, ...], ...]:
        return tuple(
            tuple(self.reconstructed_entry(i, j) for j in range(self.size))
            for i in range(self.size)
        )

    def verify(self) -> None:
        if self.size == 0:
            raise ValueError("empty matrix")
        assert_symmetric(self.matrix)
        for term in self.terms:
            if len(term.vector) != self.size:
                raise ValueError("term vector has wrong length")
            if term.weight < 0:
                raise ValueError(f"negative square weight: {term.weight}")
        rebuilt = self.reconstructed_matrix()
        if rebuilt != self.matrix:
            raise ValueError(
                "square-norm certificate does not reconstruct matrix: "
                f"expected={self.matrix}, rebuilt={rebuilt}"
            )

    def quadratic_value(self, coeffs: Sequence[Fraction]) -> Fraction:
        if len(coeffs) != self.size:
            raise ValueError("coefficient vector has wrong length")
        return sum(
            self.matrix[i][j] * coeffs[i] * coeffs[j]
            for i in range(self.size)
            for j in range(self.size)
        )

    def square_value(self, coeffs: Sequence[Fraction]) -> Fraction:
        if len(coeffs) != self.size:
            raise ValueError("coefficient vector has wrong length")
        return sum(term.value_on_coefficients(coeffs) for term in self.terms)

    def verify_quadratic_readback(self, coeffs: Sequence[Fraction]) -> Fraction:
        q = self.quadratic_value(coeffs)
        s = self.square_value(coeffs)
        if q != s:
            raise ValueError(f"quadratic readback failed: matrix={q}, squares={s}")
        if s < 0:
            raise ValueError("square value is negative, impossible with nonnegative weights")
        return s

    def to_json(self) -> dict[str, object]:
        self.verify()
        return {
            "type": "finite_source_norm_certificate",
            "size": self.size,
            "matrix": [[qstr(x) for x in row] for row in self.matrix],
            "terms": [term.to_json() for term in self.terms],
            "reconstructed_matrix": [
                [qstr(x) for x in row] for row in self.reconstructed_matrix()
            ],
            "verified": True,
            "logic": (
                "B_ij = sum_k w_k v_{k,i} v_{k,j} with w_k >= 0, hence "
                "c^T B c = sum_k w_k (v_k . c)^2 >= 0 for every rational c."
            ),
        }


def ldl_source_norm_certificate(matrix: Sequence[Sequence[Fraction]]) -> SourceNormCertificate:
    """Construct B = L D L^T exactly when no pivoting is needed.

    For semidefinite zero pivots, this accepts the case where the remaining
    column numerators are exactly zero.  More general semidefinite matrices can
    still be checked by supplying explicit square terms directly.
    """
    n = len(matrix)
    B = [[Q(matrix[i][j]) for j in range(n)] for i in range(n)]
    assert_symmetric(B)
    L = [[Fraction(0) for _ in range(n)] for _ in range(n)]
    D = [Fraction(0) for _ in range(n)]
    for i in range(n):
        L[i][i] = Fraction(1)

    for j in range(n):
        pivot = B[j][j] - sum(L[j][k] * L[j][k] * D[k] for k in range(j))
        if pivot < 0:
            raise ValueError(f"negative LDL pivot at {j}: {pivot}")
        D[j] = pivot
        for i in range(j + 1, n):
            numerator = B[i][j] - sum(L[i][k] * L[j][k] * D[k] for k in range(j))
            if pivot == 0:
                if numerator != 0:
                    raise ValueError(
                        f"zero LDL pivot at {j} but nonzero coupling to row {i}: {numerator}"
                    )
                L[i][j] = Fraction(0)
            else:
                L[i][j] = numerator / pivot

    terms = []
    for k, weight in enumerate(D):
        if weight == 0:
            continue
        vector = tuple(L[i][k] for i in range(n))
        terms.append(SourceNormTerm(weight=weight, vector=vector, label=f"LDL-column-{k}"))
    cert = SourceNormCertificate(tuple(tuple(row) for row in B), tuple(terms))
    cert.verify()
    return cert


def demo_matrix() -> list[list[Fraction]]:
    # A positive definite finite Gram packet with exact source-norm decomposition.
    return [
        [Fraction(2), Fraction(1), Fraction(1)],
        [Fraction(1), Fraction(2), Fraction(0)],
        [Fraction(1), Fraction(0), Fraction(2)],
    ]


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument(
        "--matrix-json",
        help="square rational matrix as JSON, e.g. '[[2,1],[1,2]]'",
    )
    p.add_argument(
        "--coeffs-json",
        help="optional rational coefficient vector to verify c^T B c readback",
    )
    return p


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    matrix = parse_matrix_json(args.matrix_json) if args.matrix_json else demo_matrix()
    cert = ldl_source_norm_certificate(matrix)
    out = cert.to_json()
    if args.coeffs_json:
        coeffs = [Q(x) for x in json.loads(args.coeffs_json)]
        out["coefficients"] = [qstr(x) for x in coeffs]
        out["quadratic_square_value"] = qstr(cert.verify_quadratic_readback(coeffs))
    print(json.dumps(out, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
