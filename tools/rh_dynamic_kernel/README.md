# Dynamic mirror-packet certificate checker

This directory contains the algebraic and programmatic part of the dynamic RH route.

`mirror_packet_cert.py` verifies a finite certificate:

```text
mirror pair + exact mirror-odd Lagrange filter + certified tail bound
    => strict signed Weil mirror quadratic readout
```

The checker is a consumer of the tail bound and of any eventual prime/Gamma source-positivity certificate. It does not claim to prove RH by finite sampling.

## Demo

```bash
python3 mirror_packet_cert.py --r 1/7 --gamma 14 --tail-bound 1
python3 mirror_packet_cert_tests.py
```

The output includes exact rational polynomial coefficients for the mirror-odd Lagrange filter, exact interpolation checks at `lambda_plus`, `lambda_minus`, and optional extra exponents, exact selected-pair contribution `-2*multiplicity`, and exact strict margin `2*multiplicity - tail_abs_bound`.

A positive strict margin certifies the signed conclusion under the supplied tail bound.

## Boundary

The remaining front-end is the source-side norm formula

```text
P(g*g#) + A(g*g#) = ||Psi_g^{prime,Gamma}||^2 >= 0.
```

If that formula is supplied without reading the zero set, the dynamic packet checker supplies the finite contradiction step for any separated mirror pair.
