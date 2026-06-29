#!/usr/bin/env python3
"""Reproducible negative result for the dyadic truncation LP route to RH.

This script is a counterexample artifact.  It tests the concrete finite
cutoffs

    xi_K(z) = integral_0^aK Phi(u) cos(z u) du

for the de Bruijn-Newman Fourier kernel Phi.  The refuted claim is the
all-K premise "for every K, xi_K is in the Laguerre-Polya class" for this
sharp-cutoff construction.  The computation exhibits non-real zeros of
small-K truncations, hence kappa_K > 0 in the audited boxes, so the all-K
LP premise is false.

This does not prove, disprove, or otherwise touch RH itself.  It only records
why this particular route cannot be completed by assuming all sharp dyadic
truncations are LP.  The relevant structural background is the usual warning
pattern: Montgomery 1983 on the Turan partial-sum route as a proven failure;
Szego-curve behavior for partial sums of e^z, whose zeros can be complex even
when the limit has no zeros; the de Bruijn-Newman Lambda flow, where smooth
heat factors e^(t u^2) have LP-preservation theory while sharp cutoffs do not;
Farmer 2022, Adv. Math., on Jensen routes being insensitive to RH; and the
reported PF_5 failure in arXiv:2602.20313.

The script checks both dyadic cutoff conventions encountered in the recovered
numerical audit:

    power: a_K = 2^K log 2
    sqrt:  a_K = sqrt(2^K) log 2

Run:

    python3 papers/bedc/experiments/dyadic_truncation_lp_refutation.py

Expected output includes K=1..3 rows and at least these counterexamples:

    power K=1: non-real zero near 66.3839283664 + 1.3116251915 i
    sqrt  K=1: non-real zero near 30.2985057832 + 0.8632292908 i
    sqrt  K=2: the same cutoff as power K=1, hence the same zero pair

The displayed coordinates are not read from a saved data file.  They are
recomputed by an argument-principle count in an audit rectangle, Newton
refinement from the rectangle center, and a high-precision residual check of
the finite incomplete-gamma expression for xi_K.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from typing import Callable, Iterable

import mpmath as mp


@dataclass(frozen=True)
class Rect:
    name: str
    x0: mp.mpf
    x1: mp.mpf
    y0: mp.mpf
    y1: mp.mpf

    @property
    def center(self) -> mp.mpc:
        return mp.mpc((self.x0 + self.x1) / 2, (self.y0 + self.y1) / 2)

    def contains(self, z: mp.mpc) -> bool:
        return self.x0 <= mp.re(z) <= self.x1 and self.y0 <= mp.im(z) <= self.y1

    def label(self) -> str:
        return (
            f"{self.name}=[{fmt(self.x0, 8)}, {fmt(self.x1, 8)}] x "
            f"[{fmt(self.y0, 8)}, {fmt(self.y1, 8)}]"
        )


@dataclass
class RootCertificate:
    root: mp.mpc
    residual: mp.mpf
    mirror_residual: mp.mpf
    newton_residual: mp.mpf
    count: int
    winding: mp.mpf
    winding_check: mp.mpf | None
    boundary_min_abs: mp.mpf
    box: Rect


@dataclass
class CaseResult:
    family: str
    K: int
    cutoff: mp.mpf
    boxes_checked: int
    roots: list[RootCertificate]
    zero_count_boxes: list[tuple[Rect, int, mp.mpf, mp.mpf]]


SQRT_WITNESS_BOX = Rect(
    "sqrt-K1-witness",
    mp.mpf("28"),
    mp.mpf("32"),
    mp.mpf("0.5"),
    mp.mpf("1.2"),
)

POWER_WITNESS_BOX = Rect(
    "power-K1-witness",
    mp.mpf("64"),
    mp.mpf("68"),
    mp.mpf("0.9"),
    mp.mpf("1.7"),
)


def fmt(value: mp.mpf | mp.mpc, digits: int = 18) -> str:
    return mp.nstr(value, digits, strip_zeros=False)


def set_dps(dps: int) -> None:
    mp.mp.dps = dps


def term_count(dps: int) -> int:
    # On u >= 0, the n-th Phi term is polynomial in n times exp(-pi n^2).
    # n=10 is already below 1e-130, and the extra margin covers the default
    # high-precision residual pass.
    if dps <= 80:
        return 10
    if dps <= 120:
        return 12
    return 14


def truncation_a(K: int, family: str) -> mp.mpf:
    if family == "power":
        return mp.power(2, K) * mp.log(2)
    if family == "sqrt":
        return mp.sqrt(mp.power(2, K)) * mp.log(2)
    raise ValueError(f"unknown cutoff family: {family}")


def phi_kernel(u: mp.mpf | mp.mpc, n_terms: int | None = None) -> mp.mpf | mp.mpc:
    """de Bruijn-Newman Fourier kernel used by the recovered audit."""
    if n_terms is None:
        n_terms = term_count(mp.mp.dps)
    eu2 = mp.e ** (2 * u)
    e5 = mp.e ** (mp.mpf("2.5") * u)
    e9 = mp.e ** (mp.mpf("4.5") * u)
    total: mp.mpf | mp.mpc = mp.mpf("0")
    for n in range(1, n_terms + 1):
        n2 = n * n
        total += (
            2 * mp.pi**2 * n2**2 * e9 - 3 * mp.pi * n2 * e5
        ) * mp.e ** (-mp.pi * n2 * eu2)
    return total


def complex_exp_integral(b: mp.mpf, z: mp.mpc, alpha: mp.mpf, a: mp.mpf) -> mp.mpc:
    """Integral_0^a exp(bu) exp(-alpha exp(2u)) exp(i z u) du."""
    s = (b + 1j * z) / 2
    upper = alpha * mp.e ** (2 * a)
    return mp.mpf("0.5") * alpha ** (-s) * mp.gammainc(s, alpha, upper)


def xi_trunc(z: mp.mpc, a: mp.mpf, n_terms: int | None = None) -> mp.mpc:
    """Finite sharp cutoff xi_K(z) via the incomplete-gamma expression."""
    if n_terms is None:
        n_terms = term_count(mp.mp.dps)
    z = mp.mpc(z)
    total = mp.mpc(0)
    for n in range(1, n_terms + 1):
        n2 = n * n
        alpha = mp.pi * n2

        i9_plus = complex_exp_integral(mp.mpf("4.5"), z, alpha, a)
        i9_minus = complex_exp_integral(mp.mpf("4.5"), -z, alpha, a)
        i9_cos = (i9_plus + i9_minus) / 2

        i5_plus = complex_exp_integral(mp.mpf("2.5"), z, alpha, a)
        i5_minus = complex_exp_integral(mp.mpf("2.5"), -z, alpha, a)
        i5_cos = (i5_plus + i5_minus) / 2

        total += 2 * mp.pi**2 * n2**2 * i9_cos - 3 * mp.pi * n2 * i5_cos
    return total


def boundary_points(rect: Rect, samples_per_side: int) -> list[mp.mpc]:
    points: list[mp.mpc] = []
    n = samples_per_side
    for k in range(n):
        t = mp.mpf(k) / n
        points.append(mp.mpc(rect.x0 + t * (rect.x1 - rect.x0), rect.y0))
    for k in range(n):
        t = mp.mpf(k) / n
        points.append(mp.mpc(rect.x1, rect.y0 + t * (rect.y1 - rect.y0)))
    for k in range(n):
        t = mp.mpf(k) / n
        points.append(mp.mpc(rect.x1 - t * (rect.x1 - rect.x0), rect.y1))
    for k in range(n):
        t = mp.mpf(k) / n
        points.append(mp.mpc(rect.x0, rect.y1 - t * (rect.y1 - rect.y0)))
    points.append(points[0])
    return points


def unwrap_argument_count(values: Iterable[mp.mpc]) -> mp.mpf:
    values = list(values)
    if not values:
        return mp.mpf("0")
    total = mp.mpf("0")
    previous = mp.arg(values[0])
    for value in values[1:]:
        current = mp.arg(value)
        delta = current - previous
        while delta <= -mp.pi:
            delta += 2 * mp.pi
        while delta > mp.pi:
            delta -= 2 * mp.pi
        total += delta
        previous = current
    return total / (2 * mp.pi)


def argument_count_rect(
    f: Callable[[mp.mpc], mp.mpc],
    rect: Rect,
    samples_per_side: int,
) -> tuple[int, mp.mpf, mp.mpf]:
    values = [f(point) for point in boundary_points(rect, samples_per_side)]
    winding = unwrap_argument_count(values)
    min_abs = min(abs(value) for value in values)
    return int(mp.nint(winding)), winding, min_abs


def newton_root(
    f: Callable[[mp.mpc], mp.mpc],
    z0: mp.mpc,
    max_iter: int,
    tol: mp.mpf,
) -> tuple[mp.mpc, mp.mpf, bool]:
    z = mp.mpc(z0)
    h = mp.mpf(10) ** (-(mp.mp.dps // 3))
    for _ in range(max_iter):
        fz = f(z)
        residual = abs(fz)
        if residual < tol:
            return z, residual, True
        derivative = (f(z + h) - f(z - h)) / (2 * h)
        if abs(derivative) == 0:
            return z, residual, False
        step = fz / derivative
        z -= step
        if abs(step) < tol:
            residual = abs(f(z))
            return z, residual, residual < mp.sqrt(tol)
    residual = abs(f(z))
    return z, residual, residual < mp.sqrt(tol)


def dedup_roots(roots: list[RootCertificate], tol: mp.mpf) -> list[RootCertificate]:
    out: list[RootCertificate] = []
    for root in roots:
        if all(abs(root.root - seen.root) > tol for seen in out):
            out.append(root)
    out.sort(key=lambda certificate: (float(mp.re(certificate.root)), float(mp.im(certificate.root))))
    return out


def case_boxes(family: str, K: int) -> list[Rect]:
    """Audited boxes for K=1..3.

    The boxes are witness windows, not saved root coordinates.  A positive
    real-part root in either box is mirrored to negative real part because
    xi_K is even.
    """
    if family == "power":
        return [POWER_WITNESS_BOX]
    if family == "sqrt" and K == 1:
        return [SQRT_WITNESS_BOX]
    if family == "sqrt" and K == 2:
        return [POWER_WITNESS_BOX]
    if family == "sqrt" and K == 3:
        return [SQRT_WITNESS_BOX, POWER_WITNESS_BOX]
    return []


def certify_roots_in_box(
    family: str,
    K: int,
    rect: Rect,
    samples: int,
    dps: int,
    verify_dps: int,
) -> tuple[list[RootCertificate], tuple[Rect, int, mp.mpf, mp.mpf]]:
    set_dps(dps)
    cutoff = truncation_a(K, family)
    f = lambda z: xi_trunc(z, cutoff)
    count, winding, boundary_min_abs = argument_count_rect(f, rect, samples)
    zero_count_row = (rect, count, winding, boundary_min_abs)
    if count == 0:
        return [], zero_count_row

    winding_check: mp.mpf | None = None
    check_count, winding_check, _ = argument_count_rect(f, rect, samples * 2)
    if check_count != count:
        raise RuntimeError(
            f"unstable argument count for {family} K={K} in {rect.label()}: "
            f"{count} vs {check_count}"
        )
    if count != 1:
        raise RuntimeError(
            f"expected a single witness root in {family} K={K} {rect.label()}, "
            f"found count={count}"
        )

    root, newton_residual, ok = newton_root(
        f,
        rect.center,
        max_iter=50,
        tol=mp.mpf(10) ** (-(dps // 2)),
    )
    if not ok or not rect.contains(root) or mp.im(root) <= 0:
        raise RuntimeError(
            f"Newton refinement failed for {family} K={K} in {rect.label()}: "
            f"root={root}, residual={newton_residual}"
        )

    root_re = str(mp.re(root))
    root_im = str(mp.im(root))

    set_dps(verify_dps)
    verify_cutoff = truncation_a(K, family)
    verify_f = lambda z: xi_trunc(z, verify_cutoff)
    refined, _, refined_ok = newton_root(
        verify_f,
        mp.mpc(mp.mpf(root_re), mp.mpf(root_im)),
        max_iter=60,
        tol=mp.mpf(10) ** (-(verify_dps // 2)),
    )
    if not refined_ok:
        raise RuntimeError(f"high-precision refinement failed for {family} K={K}")
    residual = abs(verify_f(refined))
    mirror = mp.mpc(-mp.re(refined), mp.im(refined))
    mirror_residual = abs(verify_f(mirror))
    certificate = RootCertificate(
        root=refined,
        residual=residual,
        mirror_residual=mirror_residual,
        newton_residual=newton_residual,
        count=count,
        winding=winding,
        winding_check=winding_check,
        boundary_min_abs=boundary_min_abs,
        box=rect,
    )
    return [certificate], zero_count_row


def run_case(
    family: str,
    K: int,
    samples: int,
    dps: int,
    verify_dps: int,
) -> CaseResult:
    boxes = case_boxes(family, K)
    roots: list[RootCertificate] = []
    zero_count_boxes: list[tuple[Rect, int, mp.mpf, mp.mpf]] = []
    for rect in boxes:
        found, zero_count_row = certify_roots_in_box(
            family,
            K,
            rect,
            samples,
            dps,
            verify_dps,
        )
        roots.extend(found)
        zero_count_boxes.append(zero_count_row)
    set_dps(verify_dps)
    cutoff = truncation_a(K, family)
    return CaseResult(
        family=family,
        K=K,
        cutoff=cutoff,
        boxes_checked=len(boxes),
        roots=dedup_roots(roots, mp.mpf("1e-20")),
        zero_count_boxes=zero_count_boxes,
    )


def print_case(result: CaseResult) -> None:
    positive_count = len(result.roots)
    symmetric_upper_count = 2 * positive_count
    status = "COUNTEREXAMPLE" if symmetric_upper_count > 0 else "no witness in audited boxes"
    print(
        f"{result.family:5s} K={result.K} "
        f"a_K={fmt(result.cutoff, 22)} "
        f"kappa_upper_audited>={symmetric_upper_count} "
        f"boxes={result.boxes_checked} {status}"
    )
    for rect, count, winding, boundary_min_abs in result.zero_count_boxes:
        print(
            f"  box {rect.label()} "
            f"arg_count={count} winding={fmt(winding, 12)} "
            f"boundary_min_abs={mp.nstr(boundary_min_abs, 8)}"
        )
    for certificate in result.roots:
        z = certificate.root
        print(
            f"  verified root z={fmt(mp.re(z), 34)} + {fmt(mp.im(z), 34)} i"
        )
        print(
            f"    |xi_K(z)|={mp.nstr(certificate.residual, 12)} "
            f"|xi_K(-Re(z)+i Im(z))|={mp.nstr(certificate.mirror_residual, 12)}"
        )
        if certificate.winding_check is not None:
            print(
                f"    argument-principle check: samples winding="
                f"{fmt(certificate.winding, 12)}, double-samples winding="
                f"{fmt(certificate.winding_check, 12)}"
            )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Exhibit non-real zeros of small sharp dyadic truncations of xi, "
            "refuting the all-K Laguerre-Polya premise for this route."
        )
    )
    parser.add_argument("--dps", type=int, default=50, help="precision for search")
    parser.add_argument(
        "--verify-dps",
        type=int,
        default=80,
        help="precision for the final residual check",
    )
    parser.add_argument(
        "--samples",
        type=int,
        default=8,
        help="boundary samples per side for argument-principle counts",
    )
    parser.add_argument(
        "--families",
        default="power,sqrt",
        help="comma-separated cutoff families to check: power,sqrt",
    )
    parser.add_argument("--min-K", type=int, default=1)
    parser.add_argument("--max-K", type=int, default=3)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.dps < 40:
        raise SystemExit("--dps must be at least 40")
    if args.verify_dps < args.dps:
        raise SystemExit("--verify-dps must be at least --dps")
    if args.samples < 8:
        raise SystemExit("--samples must be at least 8")

    families = [item.strip() for item in args.families.split(",") if item.strip()]
    for family in families:
        if family not in {"power", "sqrt"}:
            raise SystemExit(f"unknown cutoff family: {family}")

    print("dyadic truncation LP refutation: negative result")
    print("xi_K(z)=integral_0^aK Phi(u) cos(z u) du")
    print("This exhibits non-real zeros of small-K sharp cutoffs.")
    print("It does not address RH itself.")
    print(
        f"mpmath dps={args.dps}, verify_dps={args.verify_dps}, "
        f"samples_per_side={args.samples}"
    )
    print()

    all_results: list[CaseResult] = []
    for family in families:
        for K in range(args.min_K, args.max_K + 1):
            result = run_case(
                family=family,
                K=K,
                samples=args.samples,
                dps=args.dps,
                verify_dps=args.verify_dps,
            )
            all_results.append(result)
            print_case(result)
            print()

    found = any(result.roots for result in all_results)
    if not found:
        print("No non-real witness root was certified in the audited boxes.")
        return 1

    print(
        "Conclusion: at least one audited small-K truncation has kappa_K > 0; "
        "therefore the all-K Laguerre-Polya premise for this sharp dyadic "
        "truncation route is false."
    )
    print("No conclusion about RH itself is made or needed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
