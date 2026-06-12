# Window6 alpha-readout — SOURCE / EVIDENCE notes (oracle-derived)

> **Layer**: this is SOURCE / EVIDENCE metadata for the frontier conjecture
> `window6.green-spectral-response.alpha-readout-frontier`. It is oracle-derived
> (ChatGPT working sessions, 2026-06-11/12). It is **NOT** paper body and **NOT**
> cited in any BEDC/FibonacciReality chapter. The physical identification
> `R_6(D*_6) = alpha_EM^{-1}` is **not_claimed / needs_certificate**. Numerical
> proximity to 137.035999177 is a quarantined numerical observation, not a theorem.
>
> Forward-verified / definition-ready content has been mirrored into the conjecture's
> `verified_facts` and into the experiment
> `tools/fibonacci_reality/experiments/run_verify_window6_edge_flux_derivation.py`
> (anti-fit, no reverse-fit, no physical-constant assertion). These notes keep the
> provenance trail durable.

## Disposition ladder (as landed in the pipeline)

- **forward-proven** (Python enumeration, anti-fit): four-block partition (9,6,3,3);
  Foldbin tail-cube fiber -> micro cells (27,22,9,6) partition of {0..63}; hypercube
  edge matrix E; Markov kernel T; escape ratio 8/9; chi_R(0)=87/1024; Delta_R(z)
  rational function; Delta_R(1)=26401/(2^13*571); det(I-zT)=(z-1)(55z^3+506z^2-7263z-48114)/48114.
- **forward-verified** (exact rational linear algebra): D_0=47=F_9+F_7=F_10-F_6;
  q1 = -1/2 = alternating Jordan-mode eigenvalue of the explicit fold-gauge operator
  A_0 (spec {1,1/2,-1/2}, one 2x2 Jordan block, Parry kernel); A_0 is paper-sourced.
- **definition_ready** (explicit definitions, forward-verified expansion): R_6 readout
  function; GoldenLocalResponseFunctor_6 with rho_m=max{k:F_k<=2^m-1} (rho_6=10),
  s_m=m+1 (s_6=7).
- **needs_certificate**: q0=1; functor forcedness; seam/local-return forcedness;
  Delta_R'(z)>0 monotonicity; A_0 Window6 first-principles derivation.
- **not_claimed**: physical R_6(D*)=alpha_EM^{-1}; metrological comparison; full scale flow.

## A. Static residual ledger / denominator

D*_6,alpha = 47 + phi^-7 - (1/2) phi^-17 + (8/9) phi^-27
  - 47 = F_9 + F_7 = F_10 - F_6  (CoarseResidualLedger_6)
  - phi^-7 first beyond-window seam (s_6 = m+1 = 7)
  - -1/2 = alternating Jordan-mode eigenvalue of A_0 (see C)
  - 8/9 = P(leave U_R | U_R) = |dU_R|/(6|U_R|) = 32/36 (edge-flux escape)
C*_6,alpha = 1/2 + (1/4) cos^2(pi/phi) + phi^5 / D*_6,alpha
  (equivalently 1/2 + (1/4)cos^2(pi/phi) + 1/(D phi^5) in the R_6 form below)
alpha_Z6^-1(0) = 2 pi (21 + 34 C*) / (21 phi^-6 + 34 C* phi^-7) = 137.035999177006279... (NOT claimed physical)

## B. Window6 edge-flux skeleton (forward-derived, anti-fit)

X_6 = length-6 binary words with no adjacent ones, |X_6|=21.
Four-block stable decomposition (cyclic/boundary + Hamming weight):
  boundary X_6^R = {w : w_1=w_6=1} = {100001,100101,101001} (size 3)
  cyclic = X_6 \ boundary; by weight: wt=2 -> 9, wt=1 -> 6, wt in {0,3} -> 3 ; sizes (9,6,3,3).
Foldbin tail-cube fiber: V_6(w)=sum_k w_k F_{k+1};
  fiber(w) = {V_6(w)+21 c7+34 c8+55 c9 : c7c8=0, c8c9=0, w6 c7=0, <=63}.
  -> micro cells (|U_2|,|U_1|,|U_L|,|U_R|) = (27,22,9,6), partition of {0..63}.
Hypercube Q_6 edge matrix (192 edges):
  E = [[28,63,23,20],[63,21,21,6],[23,21,2,6],[20,6,6,2]].
Markov kernel: T_aa = 2 E_aa/(6|U_a|), T_ab = E_ab/(6|U_a|); pi=(27,22,9,6)/64 stationary.
  |dU_R| = 20+6+6 = 32, |U_R|=6, P(leave U_R|U_R)=32/36=8/9.
Green excess: f_R=1_R-pi_R, chi_R(z)=<f_R,(I-zT)^-1 f_R>_pi, Delta_R(z)=2(chi_R(z)-chi_R(0)).
  chi_R(0)=87/1024; Delta_R(z) = -3z(1595z^2+24477z+26730)/(512(55z^3+506z^2-7263z-48114));
  Delta_R(0)=0; Delta_R(1)=26401/(2^13*571); det(I-zT)=(z-1)(55z^3+506z^2-7263z-48114)/48114.
571 enters via SNF(L_E^red)=diag(1,1,123336), 123336=2^3*3^3*571 (dynamic Green-relaxation prime).

## C. Fold-gauge operator A_0 (forward-verified spectrum; paper-sourced operator)

A_theta (uniform-baseline mismatch-indicator weighted adjacency, three e^theta mismatch edges);
A_0 = A_theta|theta=0 = (1/2)*[[1,1,0,1],[0,0,1,0],[1,2,0,0],[1,0,0,0]].
  char(A_0) = (lam-1)(2lam-1)(2lam+1)^2 / 8 ;  spec = {1, 1/2, -1/2 (algmult 2)} ;
  rank(A_0 + (1/2)I)=3 -> geommult(-1/2)=1 -> one 2x2 Jordan block at -1/2.
  Parry kernel (right Perron r=(2,1,2,1)): P=[[1/2,1/4,0,1/4],[0,0,1,0],[1/2,1/2,0,0],[1,0,0,0]], same charpoly.
So q1 = -1/2 = alternating Jordan-mode eigenvalue. (A_0's Window6 first-principles
derivation from the four-cell mismatch structure remains a separate obligation.)

## D. GoldenLocalResponseFunctor_6 (definition_ready; forcedness needs_certificate)

rho_m := max{k : F_k <= 2^m-1} ; rho_6 = 10 (F_10=55<=63<F_11=89).
s_m := m+1 ; s_6 = 7.
Q(u) := q0 + q1 u + q2 u^2 ; current candidate Q_{6,alpha}(u) = 1 - (1/2)u + (8/9)u^2.
R_m(D_0,Q) := D_0 + phi^{-s_m} Q(phi^{-rho_m}).
  R_6(47,Q) = 47 + phi^-7(1 - (1/2)phi^-10 + (8/9)phi^-20) = 47 + phi^-7 - (1/2)phi^-17 + (8/9)phi^-27 = D*_6.
  (definition expansion, forward-verified; NOT a forcedness proof.)
R_6 readout function (explicit definition):
  C_6(D) = 1/2 + (1/4)cos^2(pi/phi) + 1/(D phi^5).
  R_6(D) = 2 pi (21 + 34 C_6(D)) / (21 phi^-6 + 34 C_6(D) phi^-7)
         = 2 pi phi^6 (21 + 34 C_6(D)) / (21 + 34 C_6(D) phi^-1).

## E. Observable-shell theorem (latest development, 2026-06-12/13)

Write A=F_8=21, B=F_9=34, and the running readout
  R(sigma,D) = 2 pi (A + B C(D)) / (A phi^-sigma + B C(D) phi^-(sigma+1))
            = 2 pi phi^sigma (A + B C(D)) / (A + B C(D) phi^-1).
So sigma is the master scale variable (it multiplies the whole readout by phi^sigma).
Low-energy static point: sigma=6, D=D*_6, z=0.

Effective-shell absorption of D-variation. With C* = C(D*_6) and
  delta_sigma_D(D) = log_phi[ (A+B C(D))/(A+B C*) * (A+B C* phi^-1)/(A+B C(D) phi^-1) ],
there is an exact identity
  R(sigma,D) = R_0 * phi^{sigma - 6 + delta_sigma_D(D)},   R_0 = R(6, D*_6).
Hence the single external scalar alpha^-1 sees only
  sigma_eff = sigma + delta_sigma_D(D).

Effective golden anomalous dimension:
  gamma_eff(Q) = 6 - sigma_eff(Q),   alpha^-1(Q) = alpha^-1(0) * phi^{-gamma_eff(Q)},
  gamma_eff(Q) = log_phi( alpha^-1(0) / alpha^-1(Q) ).
gamma_eff is the externally observable variable. Internally
  gamma_eff = gamma_sigma + gamma_D + ... ,  gamma_sigma = 6-sigma,  gamma_D = -delta_sigma_D(D).

**Observable-shell theorem (honest core).** A single scalar alpha^-1(Q) determines
only sigma_eff(Q) (equivalently gamma_eff(Q)); it does NOT uniquely split sigma_eff
into sigma + delta_sigma_D(z). Separating sigma(Q) and z(Q) requires a SECOND class
of observable (vacuum-polarization spectral function, phase-relaxation response,
Green susceptibility, parity-sensitive coherence). This is the anti-overfit
discipline made precise: one constant cannot fit many internal degrees of freedom.

Green-excess D-contribution is tiny: gamma_D(z) ~ 1.1021e-15 * z + O(z^2),
gamma_D(1) ~ 1.91e-15. So the 571-Green-excess is an internal Green susceptibility
certificate, NOT the main source of physical running. Main running must be carried
by sigma(Q) (master coordinate), not D(z).

RG dictionary: with R(Q)=alpha^-1(Q)=R_0 phi^{-gamma_eff(Q)},
  d gamma_eff / d ln Q = (1/ln phi) d ln alpha / d ln Q = beta_alpha/(alpha ln phi).
QED beta_alpha>0  =>  d gamma_eff/d ln Q > 0  (golden-shell anomalous dimension grows with Q).
Direction: Q up => sigma down => alpha^-1 down => alpha up (correct physical direction).

Unified running form (boundary condition sigma(0)=6, z(0)=0):
  alpha_Z6^-1(Q) = 2 pi (21 + 34 C_{6,alpha}(z(Q))) / (21 phi^{-sigma(Q)} + 34 C_{6,alpha}(z(Q)) phi^{-(sigma(Q)+1)}).

Honest one-line: the fine-structure constant is NOT a single Fibonacci numerology
formula; alpha(0) is a Window6 static flux-reservoir boundary condition, and the
observable running of alpha(Q) is the flow of a renormalizable effective golden phase
shell index sigma_eff(Q). D and z are internal Green/ledger certificates, appearing in
the lone alpha(Q) scalar only as a tiny sigma_eff offset. Physical identification
remains needs_certificate / not_claimed.

## Provenance pointers (evidence layer only; not cited in paper body)
- PDF main_2026-05-15: edge-flux skeleton Thm 12.393 (L108373-108443); SNF(E)=diag(1,1,3,3450)
  + Z_6 phase readout (L108452-108567); SNF(L_E^red)=diag(1,1,123336) 571-block (L108452-108466);
  A_0 spectrum / Jordan Thm 6.57 (L10572-10583); Parry r=(2,1,2,1) (L10356-10380).
- ChatGPT working sessions 2026-06-11/12 (alpha Green-running, A_0 operator, GoldenLocalResponseFunctor,
  Observable-shell theorem). Oracle/source only; physical alpha identification not claimed.
