---
slug: window6-alpha-certificate-completion
title: "Window6 alpha certificate completion"
target_paper_section:
  - papers/fibonacci_reality/parts/forced_window_structure.tex
required_reality_contacts:
required_gates:
forbidden_claims_to_check:
  - window6_alone_implies_alpha
  - boundary_escape_directly_is_response_coefficient
  - recoil_phi27_is_green_phi37_layer
ripeness: ready
---

## Direction

The forced-window alpha route should be treated as a certificate-completion
problem, not as a Window6-alone derivation of a physical fine-structure constant.

The target shape is the conditional readout:

$$
\begin{aligned}
&\mathrm{FiniteWitness}_{W6}
+\mathrm{ClockCouplingCert}
+\mathrm{ResponseFunctorCert}\\
&+\mathrm{CoefficientUseCert}
+\mathrm{PhysReadoutCert}_{\alpha}
+\mathrm{MetrologicalGaugeSelectionCert}
\Rightarrow
\alpha_{Z6}^{-1}.
\end{aligned}
$$

The finite witness may contain

$$
\begin{aligned}
D_0&=47=F_9+F_7=F_{10}-F_6,\\
s_6&=7,\\
\rho_6&=10,\\
Q_{6,\alpha}(u)&=1-\frac{1}{2}u+\frac{8}{9}u^2,\\
D_6^{*}&=47+\phi^{-7}-\frac{1}{2}\phi^{-17}+\frac{8}{9}\phi^{-27}.
\end{aligned}
$$

This finite witness is not enough to identify a physical value of $\alpha$.
The readout must keep the external carrier

$$
\begin{aligned}
M_{\alpha}=G_{10}\times Q_{\mathrm{space}}\times R_{\mathrm{space}}
\end{aligned}
$$

visible: $G_{10}$ is the clock-origin torsor, $Q_{\mathrm{space}}$ is the
response-certificate space, and $R_{\mathrm{space}}$ is the physical
representation-certificate space.

## Local theorem targets

The pipeline should decompose this direction into local targets:

1. Monotone inversion for

$$
\begin{aligned}
R_6(D)
=
2\pi
\frac{21+34C_6(D)}
{21\phi^{-6}+34C_6(D)\phi^{-7}},
\qquad
C_6(D)
=
\frac{1}{2}+\frac{1}{4}\cos^2(\pi/\phi)+\frac{1}{D\phi^5}.
\end{aligned}
$$

The expected local result is $dR_6/dD<0$, so experimental scalars have a unique
effective inverse ledger coordinate on a positive interval.

2. Exponent-gauge branch separation for

$$
\begin{aligned}
D_6^{(a)}
=
47+\phi^{-(7+a)}
-\frac{1}{2}\phi^{-(17+a)}
+\frac{8}{9}\phi^{-(27+a)},
\qquad
a=0,\ldots,9.
\end{aligned}
$$

The finite window does not select the branch internally.  If the
exponent-shift branch is treated as a numerical branch, static-impedance
metrology should be used only as an external certificate selecting $a=0$.

3. Clock-coupling boundary.  Full residue support in $\mathrm{Z}/10\mathrm{Z}$
means the finite window does not select an absolute clock origin.  The theorem
must keep $\mathrm{ClockCouplingCert}(g)$ external.

4. Coefficient-use boundary.  The values $-1/2$ and $8/9$ have finite witnesses:
the alternating Jordan-mode eigenvalue and the right-boundary escape ratio.
Those witnesses do not by themselves prove that these numbers are response
polynomial coefficients.  That step is exactly
$\mathrm{CoefficientUseCert}$.

5. Physical readout boundary.  The observable shell supplies a mathematical
scalar, but the identification with $\alpha$ must be supplied by
$\mathrm{PhysReadoutCert}_{\alpha}$.

6. Experiment path ledger.  Low-energy non-running readouts should be tracked as

$$
\begin{aligned}
D_E
=
D_{Z6}
+N_E\phi^{-27}
+\mu_E\phi^{-37}
+\cdots ,
\end{aligned}
$$

with a certificate record

$$
\begin{aligned}
\mathrm{ExperimentReadoutCert}(E)
=
\left(N_E,\mu_E,\gamma_E,\mathrm{ReadoutType}_E\right).
\end{aligned}
$$

The readout type should distinguish static impedance, magnetic moment, recoil
phase path, running alpha, and Green susceptibility.

7. Green scale separation.  The Green row

$$
\begin{aligned}
\Delta_R(1)=\frac{26401}{2^{13}\cdot571}
\end{aligned}
$$

belongs to the $\phi^{-37}$ layer and carries the 571 certificate.  Recoil-scale
$\phi^{-27}$ offsets should not be explained as Green-layer effects.

## Forbidden promotions

The pipeline must block the following promotions:

- Do not state $\mathrm{Window6}\Rightarrow\alpha$.
- Do not promote the $8/9$ boundary-escape witness into a response coefficient
  theorem without $\mathrm{CoefficientUseCert}$.
- Do not identify recoil $\phi^{-27}$ effects with the Green $\phi^{-37}$ layer.
- Do not write this direction into BEDC; it belongs to
  `papers/fibonacci_reality` unless the explicit BEDC bridge is enabled.
