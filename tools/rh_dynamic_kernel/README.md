# Dynamic kernel certificate tools

This directory contains the algebraic and programmatic part of the dynamic RH route.

## Mirror-packet obstruction checker

`mirror_packet_cert.py` verifies a finite certificate:

```text
mirror pair + exact mirror-odd Lagrange filter + certified tail bound
    => strict signed Weil mirror quadratic readout
```

The checker is a consumer of the tail bound and of any eventual prime/Gamma source-positivity certificate. It does not claim to prove RH by finite sampling.

Demo:

```bash
python3 mirror_packet_cert.py --r 1/7 --gamma 14 --tail-bound 1
python3 mirror_packet_cert_tests.py
```

The output includes exact rational polynomial coefficients for the mirror-odd Lagrange filter, exact interpolation checks at `lambda_plus`, `lambda_minus`, and optional extra exponents, exact selected-pair contribution `-2*multiplicity`, and exact strict margin `2*multiplicity - tail_abs_bound`.

A positive strict margin certifies the signed conclusion under the supplied tail bound.

## Finite source-norm checker

`source_norm_cert.py` verifies the finite square-norm front-end:

```text
finite prime/Gamma Gram entries B_ij
    + B = sum_k w_k v_k v_k^T with w_k >= 0
    => c^T B c = sum_k w_k (v_k . c)^2 >= 0
```

It can consume an explicit square-term certificate or construct one by exact rational `LDL^T` elimination when no pivoting is needed.

Demo:

```bash
python3 source_norm_cert.py --matrix-json '[[2,1],[1,2]]' --coeffs-json '[3,-5]'
python3 source_norm_cert_tests.py
```

The Lean consumer `lean4/BEDC/Derived/RHRoute/WeilSourceNormPacket.lean` proves the same finite rule in-kernel: a packet of source square terms with nonnegative weights is nonnegative on every coefficient row, and any Gram quadratic with a `RatEq` readback to that packet inherits nonnegativity.

## Remaining boundary

The remaining global front-end is to produce these finite Gram entries from the actual source ledger and then prove the cofinal limit:

```text
P(g*g#) + A(g*g#) = ||Psi_g^{prime,Gamma}||^2 >= 0.
```

The tools here remove the finite algebra from the problem. What remains is the genuine source construction: prime-power/von-Mangoldt terms, archimedean Gamma terms, pole corrections, and limit transport must populate the finite Gram matrices without reading the zero set.
