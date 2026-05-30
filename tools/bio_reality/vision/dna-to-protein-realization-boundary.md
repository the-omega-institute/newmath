---
slug: dna-to-protein-realization-boundary
title: "DNA-to-protein realization as a minimal cross-layer BEDC decomposition"
target_paper_section:
  - papers/bio_reality/parts/codon_window_reality_boundary.tex
required_reality_contacts:
  - curated.standard.code.table
  - sequence_database
  - transcript_evidence
  - protein_measurement
  - structure_experiment
  - structure_prediction
  - functional_assay
  - perturbation_data
required_gates:
  cross_layer_mediation_must_be_perturbation_validated: true
  every_cross_layer_claim_needs_falsifiable_prediction: true
  intermediate_variables_must_be_constrained_by_reality_contact_at_their_layer: true
  minimal_decomposition_over_arbitrary_fitting: true
forbidden_claims_to_check:
  - cross_layer_assertion_without_a_reality_contact_at_that_layer
  - parameter_fit_without_a_falsifiable_perturbation_prediction
  - claim_lacks_minimal_decomposition_check_against_simpler_alternatives
ripeness: ready
---

The mission is to use BEDC math to explain the full DNA-to-protein realization
chain end-to-end, not to stay isolated at code-readback. Layer boundaries are
provisional research artifacts, not the goal. The goal is the minimal,
verifiable, cross-layer decomposition.

Treat DNA-to-protein as a multi-layer dynamical system

  DNA sequence ->
  transcript / ORF ->
  codon sequence ->
  amino-acid sequence ->
  translation kinetics ->
  co-translational folding ->
  3D / ensemble structure ->
  modification / localization / interaction / function

and pose the BEDC question across all layers at once: what is the smallest
set of distinguishable intermediate variables (carrier, distinctions,
internal structure, readback) that, when fit against multi-source observation,
stably predicts protein output and survives perturbation tests
(synonymous mutation, codon shuffle, ORF perturbation, species transfer,
tRNA rescue)?

Concrete next-step conjectures the pipeline should actively pursue

1. Translation gate as the first provable cross-layer bridge from code-read.
   Codon-topology residual (delta-M with amino-acid-null control, f_3 wobble
   imbalance and f_3-tAI stress U_{f_3}, CUN-vs-UUR Leu gate, AGR-vs-AGY
   ambiguity gate after Arg/Ser composition control) must, if biologically
   real, first appear at the translation gate as a non-zero beta in
   logit P(T | x, y, c) = alpha + beta phi_{Q6}(x) + gamma Z(y, c) + epsilon,
   where T is tAI, stAI, ribosome occupancy or protein abundance, and Z is
   the amino-acid and context control. Falsifiable: beta = 0 is a real
   negative result.
2. Translation-mediated folding mediation chain. Once a translation residual
   is established, ask whether folding or function residual is mediated by
   translation residual rather than by codon-topology directly. Fit a
   mediation model and report a, b, c'. A non-trivial folding residual that
   survives translation control is the first license to cross into the
   physical layer.
3. Cross-organism context interaction. Test phi_{Q6} x psi_{tRNA}(c)
   interaction. Context-dependent sign reversal (e.g., CUN-UUR log-ratio
   inverting between human and yeast) is the BEDC signature of a
   context-sensitive translation module, not a universal sign.
4. Layer 2 ORF eligibility expansion beyond a single window. Drive
   bio-data-fetcher to acquire many curated ORF and CDS intervals across
   organisms, build matched decoys and held-out splits in the experiment,
   produce a statistically meaningful classifier performance result.

Data sources the fetcher should target

  Kazusa codon usage tables across organisms
  HIVE-CUTs / CoCoPUTs for codon-pair, dinucleotide and codon usage
  NCBI Datasets for genome, transcript, CDS, GFF3 annotation
  GtRNAdb 2.0 for tRNA gene predictions
  stAIcalc weights for species-specific wobble-corrected tAI
  Ribosome profiling repositories where available
  Mass spec / proteomics datasets paired to genome
  Public structural data and AlphaFold predictions as structural prior

Discipline that distinguishes BEDC from arbitrary parameter fitting

  Every intermediate variable must be anchored to a reality contact at its
  layer. Translation residuals require tRNA or ribo-seq data. Folding
  residuals require structural data or structural prediction with reported
  uncertainty. Function residuals require functional assay data.
  Every cross-layer claim must come with a falsifiable perturbation
  prediction. Without a perturbation that should flip or scale the residual
  in a predicted direction, the claim is parameter fitting, not minimal
  decomposition.
  Minimal decomposition must be reported against simpler alternatives.
  A proposed claim must explain why a smaller set of intermediate variables
  is insufficient.

Out-of-scope shortcuts to refuse

  Single-window or single-organism conclusions presented as universal.
  Claims about folding or function that do not pass the translation control.
  Parameter fits that do not predict any new perturbation outcome.
  Conjectures whose preconditions are only prose and never converted into a
  required-data file the fetcher can acquire.

The pipeline should keep producing finite BEDC fact rows at code-read, but
also actively propose, materialize, fetch data for, run and write back
conjectures that legitimately cross into translation, structure, and
function layers under the discipline above. The boundary that matters is
not "do not cross layers" but "every crossing carries its own reality
contact and falsifiable prediction".

## Addendum 2026-05-30: Residual Compilation Theorem

Gate is not ontology. BEDC ontology is minimal, self-compilable, incompressible
distinction. Biological relevance is defined by survival score
S_Q(r | Z) = J_0 - J_Q, not by which gate the variable comes from.

AA-quotient theorem: only q-perp (residual after the amino-acid projection
P_tau q) can survive in any DNA-to-protein model that already includes the
amino-acid sequence y = tau(x). Therefore every codon-level candidate must
first be passed through q -> q - P_tau q.

Residual decompositions of the locally verified R and M:
  R-perp covers: K_AAA / AAG, Arg AGR / CGN, Ile AUA / AUU AUC,
                 Leu (CUN union UUA) / UUG, Ser UCA / other Ser.
  M-perp covers: Ile AUA, Arg AGR, Ser UCR, Thr ACR.
M-membership collapses Leu and Lys to constants on the amino-acid fibers and
therefore cannot test CUN / UUR or AAA / AAG. M is a code-read closure object;
it is locally optimal but insufficient for protein-realization residual fits.

The R -> M = WNR cup CUN step is a residual compiler that recompiles
code-read anomalies into a different residual basis.

Concrete next-stage BEDC basis to subject to survival-score tests:
  K_AAA, Arg_AGR, Ile_AUA, Leu_CUN/UUR, Leu_UUA/UUG,
  Ser_UCR/AGY, Ser_UCA/UCG, Thr_ACR/ACY, f_3-stress.

f_3-stress only becomes a dynamical variable when context tRNA / wobble
weights break f_3 symmetry: w_c != w_{c^{f_3}}.

Pipeline implication: stop pursuing M-density or M-membership directly; pursue
each B*_Q6 basis element with its own falsifiable survival test against a
readout that includes amino-acid composition control + context variables.
