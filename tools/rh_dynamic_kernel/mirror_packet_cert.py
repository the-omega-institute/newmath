#!/usr/bin/env python3
"""
Exact finite algebra for the dynamic RH mirror-packet obstruction.

This module does NOT prove RH.  It proves/checks the hard finite algebraic
subcertificate used in the dynamic time/frequency route:

    off-line mirror pair + mirror-odd Lagrange filter + certified tail bound
        => negative Weil mirror quadratic readout.

The only non-algebraic input is the tail bound.  A separate prime/Gamma
source-positivity proof would have to show that no such negative readout can
occur for the completed zeta source kernel.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from fractions import Fraction
from typing import Sequence, Tuple


def Q(x: str | int | Fraction) -> Fraction:
    """Parse a rational literal such as '3/7', '-2', or a Fraction."""
    if isinstance(x, Fraction):
        return x
    if isinstance(x, int):
        return Fraction(x, 1)
    return Fraction(x)


def qstr(x: Fraction) -> str:
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


@dataclass(frozen=True)
class Cq:
    """Exact complex number with rational real and imaginary parts."""

    re: Fraction = Fraction(0)
    im: Fraction = Fraction(0)

    @staticmethod
    def of(re: str | int | Fraction, im: str | int | Fraction = 0) -> "Cq":
        return Cq(Q(re), Q(im))

    def __add__(self, other: "Cq") -> "Cq":
        return Cq(self.re + other.re, self.im + other.im)

    def __sub__(self, other: "Cq") -> "Cq":
        return Cq(self.re - other.re, self.im - other.im)

    def __neg__(self) -> "Cq":
        return Cq(-self.re, -self.im)

    def __mul__(self, other: "Cq") -> "Cq":
        return Cq(self.re * other.re - self.im * other.im,
                  self.re * other.im + self.im * other.re)

    def inv(self) -> "Cq":
        d = self.re * self.re + self.im * self.im
        if d == 0:
            raise ZeroDivisionError("division by zero in Cq")
        return Cq(self.re / d, -self.im / d)

    def __truediv__(self, other: "Cq") -> "Cq":
        return self * other.inv()

    def conj(self) -> "Cq":
        return Cq(self.re, -self.im)

    def mirror(self) -> "Cq":
        """The centered functional-equation mirror: lambda -> -conj(lambda)."""
        return Cq(-self.re, self.im)

    def is_real(self) -> bool:
        return self.im == 0

    def to_json(self) -> dict[str, str]:
        return {"re": qstr(self.re), "im": qstr(self.im)}

    def __repr__(self) -> str:
        if self.im == 0:
            return qstr(self.re)
        sign = "+" if self.im >= 0 else "-"
        return f"{qstr(self.re)} {sign} {qstr(abs(self.im))}i"


ZERO = Cq()
ONE = Cq(Fraction(1), Fraction(0))
NEG_ONE = Cq(Fraction(-1), Fraction(0))


@dataclass(frozen=True)
class Poly:
    """Polynomial with Cq coefficients, stored lowest degree first."""

    coeffs: Tuple[Cq, ...]

    @staticmethod
    def constant(c: Cq) -> "Poly":
        return Poly((c,)).trim()

    @staticmethod
    def monomial_root(root: Cq) -> "Poly":
        # z - root
        return Poly((-root, ONE))

    def trim(self) -> "Poly":
        coeffs = list(self.coeffs)
        while len(coeffs) > 1 and coeffs[-1] == ZERO:
            coeffs.pop()
        return Poly(tuple(coeffs))

    def __add__(self, other: "Poly") -> "Poly":
        n = max(len(self.coeffs), len(other.coeffs))
        out = []
        for i in range(n):
            a = self.coeffs[i] if i < len(self.coeffs) else ZERO
            b = other.coeffs[i] if i < len(other.coeffs) else ZERO
            out.append(a + b)
        return Poly(tuple(out)).trim()

    def __mul__(self, other: "Poly") -> "Poly":
        out = [ZERO for _ in range(len(self.coeffs) + len(other.coeffs) - 1)]
        for i, a in enumerate(self.coeffs):
            for j, b in enumerate(other.coeffs):
                out[i + j] = out[i + j] + (a * b)
        return Poly(tuple(out)).trim()

    def scale(self, c: Cq) -> "Poly":
        return Poly(tuple(c * a for a in self.coeffs)).trim()

    def eval(self, z: Cq) -> Cq:
        acc = ZERO
        for c in reversed(self.coeffs):
            acc = acc * z + c
        return acc

    def degree(self) -> int:
        return len(self.coeffs) - 1

    def to_json(self) -> list[dict[str, str]]:
        return [c.to_json() for c in self.coeffs]


def lagrange(points: Sequence[Cq], values: Sequence[Cq]) -> Poly:
    if len(points) != len(values):
        raise ValueError("points and values must have equal length")
    if len(set(points)) != len(points):
        raise ValueError("Lagrange points must be distinct")
    total = Poly.constant(ZERO)
    for j, (xj, yj) in enumerate(zip(points, values)):
        basis = Poly.constant(ONE)
        denom = ONE
        for k, xk in enumerate(points):
            if k == j:
                continue
            basis = basis * Poly.monomial_root(xk)
            denom = denom * (xj - xk)
        total = total + basis.scale(yj / denom)
    return total.trim()


@dataclass(frozen=True)
class MirrorPacketCertificate:
    r: Fraction
    gamma: Fraction
    multiplicity: int
    killers: Tuple[Cq, ...]
    tail_abs_bound: Fraction

    def lambda_plus(self) -> Cq:
        return Cq(self.r, self.gamma)

    def lambda_minus(self) -> Cq:
        return Cq(-self.r, self.gamma)

    def points_and_values(self) -> tuple[list[Cq], list[Cq]]:
        pts = [self.lambda_plus(), self.lambda_minus(), *self.killers]
        vals = [ONE, NEG_ONE] + [ZERO for _ in self.killers]
        return pts, vals

    def polynomial(self) -> Poly:
        pts, vals = self.points_and_values()
        return lagrange(pts, vals)

    def selected_contribution(self) -> Cq:
        """Selected pair contribution to the mirror quadratic form."""
        p = self.polynomial()
        lp = self.lambda_plus()
        lm = self.lambda_minus()
        term = p.eval(lp) * p.eval(lp.mirror()).conj()
        term = term + p.eval(lm) * p.eval(lm.mirror()).conj()
        return Cq(Fraction(self.multiplicity), 0) * term

    def margin(self) -> Fraction:
        selected = self.selected_contribution()
        if not selected.is_real():
            raise ValueError(f"selected contribution not real: {selected}")
        # total real part <= selected + |tail|.  Negative if this is < 0.
        return -selected.re - self.tail_abs_bound

    def verifies_negative(self) -> bool:
        return self.r != 0 and self.multiplicity > 0 and self.margin() > 0

    def to_json(self) -> dict:
        p = self.polynomial()
        pts, vals = self.points_and_values()
        evals = [p.eval(z) for z in pts]
        selected = self.selected_contribution()
        return {
            "type": "dynamic_mirror_packet_certificate",
            "r": qstr(self.r),
            "gamma": qstr(self.gamma),
            "multiplicity": self.multiplicity,
            "lambda_plus": self.lambda_plus().to_json(),
            "lambda_minus": self.lambda_minus().to_json(),
            "killers": [z.to_json() for z in self.killers],
            "polynomial_degree": p.degree(),
            "polynomial_coefficients_low_to_high": p.to_json(),
            "interpolation_points": [z.to_json() for z in pts],
            "interpolation_target_values": [v.to_json() for v in vals],
            "interpolation_evaluated_values": [v.to_json() for v in evals],
            "selected_pair_contribution": selected.to_json(),
            "tail_abs_bound": qstr(self.tail_abs_bound),
            "negative_margin": qstr(self.margin()),
            "verifies_negative_weil_readout": self.verifies_negative(),
            "logic": (
                "If the remote zero-side mirror tail has absolute value at most "
                "tail_abs_bound, then total_real <= selected_pair_contribution + "
                "tail_abs_bound.  A positive negative_margin proves total_real < 0."
            ),
        }


def parse_cq_pair(text: str) -> Cq:
    """Parse 'a,b' as a + bi with rationals a,b."""
    parts = text.split(",")
    if len(parts) != 2:
        raise argparse.ArgumentTypeError("complex rational must be 're,im'")
    return Cq.of(parts[0].strip(), parts[1].strip())


def build_arg_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--r", default="1/7", help="nonzero rational radial coordinate")
    p.add_argument("--gamma", default="14", help="rational height coordinate")
    p.add_argument("--multiplicity", type=int, default=1)
    p.add_argument(
        "--killer",
        action="append",
        default=[],
        type=parse_cq_pair,
        help="extra exponent to kill, written 're,im'; may be repeated",
    )
    p.add_argument("--tail-bound", default="1", help="certified absolute tail bound")
    return p


def main(argv: Sequence[str] | None = None) -> int:
    args = build_arg_parser().parse_args(argv)
    cert = MirrorPacketCertificate(
        r=Q(args.r),
        gamma=Q(args.gamma),
        multiplicity=args.multiplicity,
        killers=tuple(args.killer),
        tail_abs_bound=Q(args.tail_bound),
    )
    print(json.dumps(cert.to_json(), indent=2, sort_keys=True))
    return 0 if cert.verifies_negative() else 2


if __name__ == "__main__":
    raise SystemExit(main())
