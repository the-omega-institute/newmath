# Residual-Uplift Cokernel Audit — Frozen Pre-Registration

Algebra-first protocol for the B\*_Q6 codon → protein-abundance residual. This document freezes the
algebraic objects, the acceptance gates, and the certified-vs-coincidence criterion **before** any
compiler is fit or any characteristic polynomial is inspected. Its purpose is to make a future
`alpha_U -> finite-state compiler -> chi_U(lambda)` audit *certifiable* rather than data-reverse-engineering.
Frozen at commit time; do not edit gate definitions after inspecting any recurrence result — a changed gate
after seeing an outcome invalidates certification and downgrades the run to `coincidence`.

## Epistemic stance

Data proves a fixed algebraic idea; data does not generate theorem-shaped objects. The reversed arrow
(letting a searched state graph over a noisy residual "discover" a golden polynomial) is the failure mode
this protocol exists to prevent — it is the same failure as the bridge's `BC1` (a Fibonacci count match that
is encoding-independent and therefore forces nothing about the genetic code). Verdict vocabulary matches the
bridge: `certified` / `refuted` / `coincidence` / `needs_derivation` / `needs_data`.

## Algebraic objects (single source of truth)

- `V_P` — protein-abundance residual space (per organism, after fixed controls: length, aa-composition, GC3, M-density).
- `A_P` — subspace spanned by the measured-readout dictionary D = {measured TE, mRNA stability, turnover, PTM, localization, complex, TM, domain, mRNA abundance}.
- `H_P = V_P / A_P` — the quotient (cokernel space). The object of interest is the class `[P_Q] in H_P`.
- `Q` — the 9 B\*_Q6 synonymous-residual source axes {K_AAA, Arg_AGR, Ile_AUA, Leu_CUN/UUR, Leu_UUA/UUG, Ser_UCR/AGY, Ser_UCA/UCG, Thr_ACR/ACY, f3_stress}, each amino-acid-quotiented (per-fiber mean subtracted; `project_syn`).
- `P_Q = Pi_Q P` — protein-abundance component projected onto Q.
- `U = P_Q - Pi_D P_Q` — the unexplained residual (the cokernel representative to be lifted).
- `alpha_U = (Q^T Q)^+ Q^T U` — source-side pullback of U onto the 9 coordinates (Moore-Penrose). **Computed only from U**, never substituted by regressing execution/selection channels directly on P_Q.
- `q_U(t) = alpha_U . q(c_t)` — per-codon source stream.
- `s_{t+1} = F(s_t, q_U(t))` — minimal finite-state compiler; `chi_U(lambda) = det(lambda I - A_U)` its transition-graph characteristic polynomial.

## Frozen decision

The audit `A` (alpha_U -> compiler -> chi_U recurrence check) is **NOT run** until every gate below passes.
Until then the status of `A` is `needs_derivation` — never a soft positive. This decision is the output of a
three-perspective isolated-worker consensus (minimal/structural/delete): all three judged that running the
compiler on the current U would be data-reverse-engineering / numerology.

## Grounded negatives on record (why the gates exist)

- Bridge `BC1` = coincidence (64->21<->F8, |R|=13<->F7 count match is encoding-independent); `BC2` = refuted; `BC3` = needs_derivation.
- `residual_basis_extraction`: all 4 organisms (yeast/E.coli/human/Danio) persistent, final_rho >= 0.972 — the readout dictionary does not compress P_Q.
- `residual_exec_selection_joint`: composition_artifact — unresolved_fraction 0.940, exec 0.044, sel 0.016; held-out delta_R2 0.0141 clears null but fails the 0.01 effect floor after DL.
- `finite_state_dwell_transducer`: delta_R2 0.00104 (~2x null), 5'-head-window footprint-density proxy only, not full-CDS, no causal claim.
- Data gaps: full-CDS per-codon A-site occupancy is not a stdlib-parseable single table; a clean U observation ceiling needs same-condition technical-replicate proteomics, absent in-repo.

## Anti-numerology gates (all must pass before `A` can certify)

1. **Freeze-before-mining.** All objects above, the allowed source alphabet, the state-update grammar, the max order/state-count, the MDL rule, the train/test splits, and the single `chi_U` endpoint are declared here before any data-mining. No phi / 571 / Z6 / Window6 constants, no Fibonacci / no-adjacent-one features, and no nucleotide-encoding choice may enter the bio-side construction objective.
2. **U observation ceiling.** Estimated from same-condition technical-replicate proteomics (NOT SD-vs-YEPD condition contrast). Require split-half / replicate reliability of U above the measurement-error floor with a pre-declared lower confidence bound. If replicate data are unavailable, the verdict is `needs_data` — not a soft positive.
3. **U-level target-permutation ceiling.** Within matched strata (abundance decile x CDS length x aa-composition x GC3/M-density x organism/condition/batch x dictionary join), recompute D, U, alpha_U, compiler, and chi_U for every permuted target; the observed endpoint must exceed the full-pipeline null after family-wise correction.
4. **Effect-size + DL gate before recurrence.** alpha_U / compiler must clear held-out prediction and description-length penalties with a pre-declared practical floor (at least the existing 0.01 delta_R2-style gate). Sub-0.1%-scale residual prediction cannot license a polynomial claim.
5. **alpha_U pullback stability.** Computed only from frozen quotient residuals U; non-saturated rank; sign/direction stable across bootstrap / condition / organism splits; coordinates not selected after seeing the recurrence result.
6. **Compiler pre-registration + cross-fitting.** Minimal deterministic finite-state compiler chosen by locked MDL/BIC on training folds only; state count, transition construction, pruning, and polynomial extraction frozen before held-out evaluation; no search over encodings, Markov orders, alphabets, sign conventions, or state lumpings after seeing chi_U.
7. **Layer-matched readout.** Full-CDS per-codon A-site occupancy (or a pre-declared equivalent same-CDS kinetic contact) for compiler learning; a 5'-head footprint-density proxy can only support a bounded operator-level finite-row record, never a translation/dwell mechanism or abundance-residual forcing claim.
8. **Exact symbolic characteristic polynomial.** `chi_U(lambda)` computed exactly from the frozen learned/derived finite graph; `lambda^2 - lambda - 1` counts only as an **exact forced factor** of the minimal/observable component polynomial (with reported multiplicity and component membership), never an approximate phi eigenvalue or a fitted scalar.
9. **Matched null + search correction.** Compare chi_U against degree/state-count/MDL-matched random automata, within-family synonymous shuffles, codon-label relabelings, alternative nucleotide encodings, and the full family of tried compiler classes; correct family-wise for every searched audit and endpoint. If matched nulls produce the factor at comparable rate, verdict is `coincidence`.
10. **Representation stability + negative discipline.** The frozen procedure must reproduce the factor or refute it across technical replicates and at least one independent condition/organism where U passes the observation gate; it must collapse under coordinate-destroying controls. Negative outcomes are terminal records (`refuted` / `coincidence` / `needs_derivation` / `needs_data`), never tuning prompts.

## Certified-vs-coincidence criterion

- **certified** iff a pre-registered frozen algebraic construction *proves* the source-side transition object has a forced characteristic factor `lambda^2 - lambda - 1` (a necessity argument independent of the biological target values), U has first passed the observation-ceiling + U-level target-permutation + effect/DL gates, the factor appears in the *exact* chi_U of the frozen observable state graph, it reproduces on held-out/replicate data, and it beats matched null / search / encoding / endpoint controls with multiplicity correction.
- **coincidence** iff the factor appears only after model/encoding/state/endpoint search, as an approximate phi match, under an unreliable U, via Window6-constant priors, or without full-pipeline null correction. Count/eigenvalue resemblance alone is never certified.
- **refuted** iff the gates pass and the frozen audit does not produce the factor/effect.
- **needs_derivation** iff the quotient/pullback/compiler/forcing construction is not yet built; **needs_data** iff the observation-ceiling replicate data or the full-CDS A-site layer are missing. These are the honest current labels.

## Immediate consequences

- The bio-side residual-uplift audit `A` is `needs_data` today (observation-ceiling replicate proteomics + full-CDS A-site both absent). It is not built on the current unresolved U.
- The Fibonacci contact is pursued, if at all, on the mathematics/bridge side as a forcing certificate (`BC1` needs an encoding-specific structural map, not a count; `BC3` foldbin needs derivation), with the biology serving only as a pre-registered falsification target.
