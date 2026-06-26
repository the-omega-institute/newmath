import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Riemann zeta / RH axiom ledger

This module is audit-only boundary data. It imports mathlib's Riemann zeta
surface and records the axiom footprint of the mathlib objects consumed by
the BEDC RH route discussion. It deliberately exports no BEDC-to-mathlib
bridge theorem.

Measured in this checkout with `#print axioms`:

* `riemannZeta`: `[propext, Classical.choice, Quot.sound]`
* `RiemannHypothesis`: `[propext, Classical.choice, Quot.sound]`
* `auditCriticalLinePredicate`: `[propext, Classical.choice, Quot.sound]`
* `auditCriticalStripPredicate`: `[propext, Classical.choice, Quot.sound]`
* `auditZetaZeroPredicate`: `[propext, Classical.choice, Quot.sound]`
* `auditZetaZeroSet`: `[propext, Classical.choice, Quot.sound]`
* `auditNontrivialZetaZeroPredicate`: `[propext, Classical.choice, Quot.sound]`
* `auditRiemannZetaAnalyticContinuationStatement`:
  `[propext, Classical.choice, Quot.sound]`
* `differentiableAt_riemannZeta`: `[propext, Classical.choice, Quot.sound]`
* `completedRiemannZeta₀`: `[propext, Classical.choice, Quot.sound]`
* `differentiable_completedZeta₀`: `[propext, Classical.choice, Quot.sound]`
* `zeta_eq_tsum_one_div_nat_add_one_cpow`:
  `[propext, Classical.choice, Quot.sound]`

RH obligation ledger:

* Zeta carrier and analytic continuation: mathlib `riemannZeta`,
  `completedRiemannZeta₀`, `differentiableAt_riemannZeta`, and the
  right-half-plane Dirichlet-series agreement all carry
  `[propext, Classical.choice, Quot.sound]`. BEDC shadows this axis through
  `RHRoute.EventflowCertificate`, `RHRoute.RecursiveTower`,
  `RHRoute.FinitePrimeWindow`, and `RHRoute.UnitaryBalance`. The constructive
  bridge stops before identifying ledgered zeta rows with the host function.
* Zero fiber: the predicate `riemannZeta s = 0`, the zero set, and the
  non-trivial-zero predicate carry the same footprint. BEDC shadows this axis
  through `RHRoute.LocalGlobalExclusion` and `RHRoute.ChannelNormalForm`.
* Strip and fixed-half readout: critical-strip and critical-line predicates
  carry the same footprint. BEDC shadows this axis through
  `RHRoute.HaltingBoundary`, `RHRoute.CounterexampleSafety`, and
  `RHRoute.NonfixedOrbit`.
* RH proposition: mathlib has the named declaration `RiemannHypothesis`, with
  the same footprint. BEDC shadows it as a fixed-half section over typed
  non-trivial zero packets. The equivalence between that constructive
  restatement and classical RH is a boundary statement here, not a bridge
  theorem.
-/

namespace BedcMathlibBridge.Boundary.RiemannZetaAxiomLedger

open Complex
open scoped BigOperators Topology Real

noncomputable section

def auditCriticalLinePredicate (s : ℂ) : Prop :=
  s.re = (1 / 2 : ℝ)

def auditCriticalStripPredicate (s : ℂ) : Prop :=
  0 < s.re ∧ s.re < 1

def auditZetaZeroPredicate (s : ℂ) : Prop :=
  riemannZeta s = 0

def auditZetaZeroSet : Set ℂ :=
  {s | riemannZeta s = 0}

def auditNontrivialZetaZeroPredicate (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ ¬∃ n : ℕ, s = -2 * (n + 1) ∧ s ≠ 1

def auditRiemannHypothesisStatement : Prop :=
  RiemannHypothesis

def auditRiemannZetaAnalyticContinuationStatement : Prop :=
  ∀ s : ℂ, s ≠ 1 → DifferentiableAt ℂ riemannZeta s

def auditCompletedRiemannZetaEntireStatement : Prop :=
  Differentiable ℂ completedRiemannZeta₀

def auditRiemannZetaDirichletSeriesAgreementStatement : Prop :=
  ∀ s : ℂ, 1 < s.re → riemannZeta s = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ s

#print axioms riemannZeta
#print axioms RiemannHypothesis
#print axioms auditCriticalLinePredicate
#print axioms auditCriticalStripPredicate
#print axioms auditZetaZeroPredicate
#print axioms auditZetaZeroSet
#print axioms auditNontrivialZetaZeroPredicate
#print axioms auditRiemannHypothesisStatement
#print axioms auditRiemannZetaAnalyticContinuationStatement
#print axioms differentiableAt_riemannZeta
#print axioms auditCompletedRiemannZetaEntireStatement
#print axioms completedRiemannZeta₀
#print axioms differentiable_completedZeta₀
#print axioms auditRiemannZetaDirichletSeriesAgreementStatement
#print axioms zeta_eq_tsum_one_div_nat_add_one_cpow

#check riemannZeta
#check RiemannHypothesis
#check differentiableAt_riemannZeta
#check completedRiemannZeta₀
#check differentiable_completedZeta₀
#check zeta_eq_tsum_one_div_nat_add_one_cpow

end

end BedcMathlibBridge.Boundary.RiemannZetaAxiomLedger
