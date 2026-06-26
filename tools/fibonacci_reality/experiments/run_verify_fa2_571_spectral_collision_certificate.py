#!/usr/bin/env python3
"""Verify the pinned automath F-A2 certificate snapshot."""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

import sympy as sp
from sympy.matrices.normalforms import smith_normal_form


EXPECTED_COMMIT = "caa043a7733205c0152ec685d9e1870697077b70"
EXPECTED_LEAN_PATH = "lean4/Omega/GroupUnification/Window6ModpstarSpectralCollision.lean"
EXPECTED_OBJECT = "paper_window6_modpstar_spectral_collision"
SNAPSHOT_PATH = (
    "tools/fibonacci_reality/data/"
    "automath_cert_window6_modpstar_571_spectral_collision.json"
)
MODULUS = 571
EDGE_MATRIX = sp.Matrix(
    [
        [28, 63, 23, 20],
        [63, 21, 21, 6],
        [23, 21, 2, 6],
        [20, 6, 6, 2],
    ]
)
EXPECTED_LAPLACIAN_REDUCED = sp.Matrix(
    [
        [106, -63, -23],
        [-63, 90, -21],
        [-23, -21, 50],
    ]
)
EXPECTED_SNF = [1, 1, 123336]
EXPECTED_CHI_COEFFS = [1, -246, 14401, -123336]
EXPECTED_DERIVATIVE_AT_ZERO_MOD_571 = 126


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": passed, "reason": reason}


def laplacian_reduced(edge_matrix: sp.Matrix) -> sp.Matrix:
    row_sums = [sum(edge_matrix.row(i)) for i in range(edge_matrix.rows)]
    laplacian = sp.diag(*row_sums) - edge_matrix
    return laplacian[:-1, :-1]


def local_arithmetic_result() -> dict[str, Any]:
    t = sp.Symbol("t")
    reduced = laplacian_reduced(EDGE_MATRIX)
    snf_matrix = smith_normal_form(reduced, domain=sp.ZZ)
    snf_diag = [int(snf_matrix[i, i]) for i in range(snf_matrix.rows)]
    characteristic = reduced.charpoly(t).as_expr()
    characteristic_coeffs = [int(c) for c in sp.Poly(characteristic, t, domain=sp.ZZ).all_coeffs()]
    characteristic_derivative = sp.diff(characteristic, t)
    characteristic_at_zero_mod = int(characteristic.subs(t, 0)) % MODULUS
    derivative_at_zero_mod = int(characteristic_derivative.subs(t, 0)) % MODULUS
    gcd_poly = sp.gcd(
        sp.Poly(characteristic, t, modulus=MODULUS),
        sp.Poly(characteristic_derivative, t, modulus=MODULUS),
    )
    det = int(reduced.det())

    return {
        "edge_matrix": [[int(edge_matrix_entry) for edge_matrix_entry in row] for row in EDGE_MATRIX.tolist()],
        "reduced_laplacian": [[int(entry) for entry in row] for row in reduced.tolist()],
        "snf": snf_diag,
        "det": det,
        "factorization": {"2": 3, "3": 3, "571": 1},
        "chi_L": str(characteristic),
        "chi_L_coefficients": characteristic_coeffs,
        "chi_L_prime": str(characteristic_derivative),
        "chi_L_0_mod571": characteristic_at_zero_mod,
        "chi_L_prime_at_0_mod571": derivative_at_zero_mod,
        "gcd_chi_L_chi_L_prime_mod571": str(gcd_poly.as_expr()),
        "gcd_deg": int(gcd_poly.degree()),
    }


def main() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    snapshot_path = repo_root / SNAPSHOT_PATH
    if not snapshot_path.exists():
        print(json.dumps({"status": "needs_data", "checks": [], "result": {"missing": str(snapshot_path)}}))
        return

    try:
        snapshot = json.loads(snapshot_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        print(json.dumps({"status": "error", "checks": [], "result": {"error": str(exc)}}))
        return

    excerpt = str(snapshot.get("captured_excerpt") or "")
    object_name = str(snapshot.get("object") or "")
    theorem_present = f"theorem {object_name}" in excerpt or f"lemma {object_name}" in excerpt
    has_forbidden_token = re.search(r"\bsorry\b|\badmit\b", excerpt) is not None
    certificate_ok = theorem_present and not has_forbidden_token

    ref_ok = (
        snapshot.get("object") == EXPECTED_OBJECT
        and snapshot.get("lean_path") == EXPECTED_LEAN_PATH
        and snapshot.get("commit") == EXPECTED_COMMIT
    )
    arithmetic = local_arithmetic_result()
    reduced_ok = arithmetic["reduced_laplacian"] == [
        [int(entry) for entry in row] for row in EXPECTED_LAPLACIAN_REDUCED.tolist()
    ]
    snf_ok = arithmetic["snf"] == EXPECTED_SNF and arithmetic["det"] == EXPECTED_SNF[-1]
    characteristic_ok = arithmetic["chi_L_coefficients"] == EXPECTED_CHI_COEFFS
    mod571_singularity_ok = (
        arithmetic["det"] % MODULUS == 0
        and arithmetic["chi_L_0_mod571"] == 0
    )
    simple_not_repeated_ok = (
        arithmetic["gcd_deg"] == 0
        and arithmetic["chi_L_prime_at_0_mod571"] == EXPECTED_DERIVATIVE_AT_ZERO_MOD_571
        and arithmetic["chi_L_prime_at_0_mod571"] != 0
    )

    checks = [
        check(
            "automath_certificate_present_sorry_free",
            certificate_ok,
            "certificate theorem is present and no sorry/admit token appears"
            if certificate_ok
            else "certificate theorem is absent or contains a sorry/admit token",
        ),
        check(
            "automath_certificate_ref_matches",
            ref_ok,
            "snapshot object, Lean path, and commit match the pinned certificate"
            if ref_ok
            else "snapshot object, Lean path, or commit differs from the pinned certificate",
        ),
        check(
            "reduced_laplacian_matches_window6_edge_matrix",
            reduced_ok,
            "reduced Laplacian is D-A with the final row and column removed from the 4-cell edge matrix"
            if reduced_ok
            else "reduced Laplacian differs from D-A with the final row and column removed",
        ),
        check(
            "smith_normal_form_factorization",
            snf_ok,
            "SNF(L_red)=diag(1,1,123336) and det(L_red)=123336=2^3*3^3*571"
            if snf_ok
            else "SNF or determinant differs from diag(1,1,123336)",
        ),
        check(
            "characteristic_polynomial",
            characteristic_ok,
            "chi_L(t)=t^3 - 246*t^2 + 14401*t - 123336"
            if characteristic_ok
            else "characteristic polynomial coefficients differ from the expected integer polynomial",
        ),
        check(
            "mod571_singularity",
            mod571_singularity_ok,
            "571 divides det(L_red), so chi_L(0)=0 mod 571 and L_red is singular over F_571"
            if mod571_singularity_ok
            else "571 does not witness singularity by determinant and chi_L(0)",
        ),
        check(
            "simple_not_repeated",
            simple_not_repeated_ok,
            "gcd(chi_L, chi_L') over F_571 has degree 0 and chi_L'(0)=14401=126 mod 571 is nonzero"
            if simple_not_repeated_ok
            else "zero root is not certified simple over F_571",
        ),
    ]
    status = "passed" if all(item["passed"] for item in checks) else "failed"
    result = {
        "status": status,
        "checks": checks,
        "result": {
            "snapshot": SNAPSHOT_PATH,
            "object": EXPECTED_OBJECT,
            "lean_path": EXPECTED_LEAN_PATH,
            "commit": EXPECTED_COMMIT,
            "local_arithmetic": arithmetic,
        },
    }
    print(json.dumps(result, ensure_ascii=False))


if __name__ == "__main__":
    main()
