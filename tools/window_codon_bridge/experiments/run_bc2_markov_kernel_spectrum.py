#!/usr/bin/env python3
"""BC2: does the Window6 coarse Markov kernel spectrum equal the bio codon-Q6 spectral scalars?

Pure-math bridge derivation. Reads two finite objects already in the papers:
- MATH side (fibonacci_reality forced_window_structure): 4-cell coarse Markov kernel T,
  cells (U2,U1,UL,UR) with |U|=(27,22,9,6) and symmetric edge matrix E; T row-stochastic.
- BIO side (bio_reality window_six_codon_tiles): spectral scalars lambda_M, lambda_R, mu.

Verdict semantics (bridge, anti-numerology):
  certified  : a structural forcing correspondence holds (here: spectra match AND a map argument exists)
  refuted    : the proposed correspondence is false (spectra do not match)
  coincidence: numbers coincide but no structural forcing (must be flagged, not a result)
  needs_derivation: cannot evaluate yet

This script computes T's spectrum (pure python, no numpy) and compares to the bio scalars.
"""
from __future__ import annotations
import json, sys, cmath
from fractions import Fraction as Fr

EXPERIMENT_ID = "bc2_markov_kernel_spectrum"
CLAIM_ID = "bridge.window6_codon_q6.spectral_correspondence"

# MATH side: edge matrix E and cell sizes (from window6-markov-kernel-coarse-spectrum-fibonacci-leading)
E = [[28, 63, 23, 20], [63, 21, 21, 6], [23, 21, 2, 6], [20, 6, 6, 2]]
U = [27, 22, 9, 6]
# BIO side: spectral scalars (from window_six_codon_tiles_at_the_code_layer)
BIO = {"lambda_M": 0.6752479308830213, "lambda_R": 0.4758352843197002, "mu": 3.051487585298128}
MATCH_TOL = 0.02


def emit(status, **kw):
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, ensure_ascii=False))
    sys.exit(0 if status in ("certified", "coincidence") else (2 if status == "refuted" else 3))


def matmul(A, B):
    n = len(A)
    return [[sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]


def main():
    n = 4
    # row-stochastic kernel T: T_aa = 2E_aa/(6|U_a|), T_ab = E_ab/(6|U_a|)
    T = [[Fr((2 * E[a][b]) if a == b else E[a][b], 6 * U[a]) for b in range(n)] for a in range(n)]
    rowsums = [sum(T[a]) for a in range(n)]
    if any(s != 1 for s in rowsums):
        emit("needs_derivation", reason="kernel not row-stochastic", rowsums=[str(s) for s in rowsums])
    # Faddeev-LeVerrier char poly: p(x)=sum c[i] x^i, c[n]=1
    M = [[Fr(1) if i == j else Fr(0) for j in range(n)] for i in range(n)]
    c = [Fr(0)] * (n + 1)
    c[n] = Fr(1)
    for k in range(1, n + 1):
        AM = matmul(T, M)
        ck = -sum(AM[i][i] for i in range(n)) / k
        c[n - k] = ck
        M = [[AM[i][j] + (ck if i == j else Fr(0)) for j in range(n)] for i in range(n)]
    a = [float(c[i]) for i in range(n + 1)]
    # Durand-Kerner roots
    roots = [cmath.exp(2j * cmath.pi * k / n) * (0.4 + 0.9j) for k in range(n)]
    for _ in range(800):
        new = []
        for i in range(n):
            num = sum(a[j] * roots[i] ** j for j in range(n + 1))
            den = 1
            for j in range(n):
                if j != i:
                    den *= (roots[i] - roots[j])
            new.append(roots[i] - num / den)
        roots = new
    eig = sorted((z.real for z in roots if abs(z.imag) < 1e-6), reverse=True)
    subdominant = [x for x in eig if abs(x - 1.0) > 1e-5]
    bio_vals = [BIO["lambda_M"], BIO["lambda_R"]]
    # try to match each bio lambda (<1) to a subdominant eigenvalue
    matches = []
    for bv in bio_vals:
        best = min(subdominant, key=lambda x: abs(x - bv)) if subdominant else None
        matches.append({"bio": bv, "nearest_kernel_eig": best, "gap": (abs(best - bv) if best is not None else None)})
    spectra_match = all(m["gap"] is not None and m["gap"] <= MATCH_TOL for m in matches)
    mu_is_stochastic_eig = BIO["mu"] <= 1.0 + MATCH_TOL  # mu=3.05 > 1 cannot be a stochastic eigenvalue
    checks = [
        {"name": "kernel_spectrum_computed", "passed": True, "eigenvalues": [round(x, 6) for x in eig]},
        {"name": "lambda_match_subdominant", "passed": spectra_match, "matches": matches, "tol": MATCH_TOL},
        {"name": "mu_admissible_as_eigenvalue", "passed": mu_is_stochastic_eig, "mu": BIO["mu"],
         "note": "stochastic-kernel eigenvalues are <=1; mu>1 cannot be one"},
    ]
    if spectra_match and mu_is_stochastic_eig:
        # even a numeric match would only be 'coincidence' until a forcing map is supplied
        emit("coincidence", checks=checks, kernel_eigenvalues=[round(x, 6) for x in eig], bio=BIO,
             note="numeric match found but NO structural forcing map yet; flagged coincidence, not certified")
    emit("refuted", checks=checks, kernel_eigenvalues=[round(x, 6) for x in eig], bio=BIO,
         reason="bio spectral scalars are not the coarse Markov kernel spectrum (subdominant eig do not match lambda; mu>1 is not a stochastic eigenvalue)",
         refined_next="BC2-R1: identify bio's actual lambda construction + try Window6 transfer-operator Perron spectrum / Green response instead of the coarse Markov kernel")


if __name__ == "__main__":
    main()
