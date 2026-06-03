import BEDC.MetaCIC.Consistency
import BEDC.MetaCIC.ClosurePreservation
import BEDC.MetaCIC.SubjectReduction
import BEDC.MetaCIC.SubjectReduction.DischargeBundle
import BEDC.MetaCIC.SubjectReduction.ObstructionLedger
import BEDC.MetaCIC.ClosedTerm
import BEDC.MetaCIC.Normalization

namespace BEDC.MetaCIC.Audit

/-! ## Re-exports of MetaCIC audit theorems

This module re-exports the BEDC.MetaCIC audit-relevant theorems
in a single namespace for downstream consumers. -/

-- Consistency
export BEDC.MetaCIC (no_closed_normal_proof_of_false closed_normal_consistency_assembly closed_consistency_reduction_obstruction_not_available)

-- Subject reduction
export BEDC.MetaCIC (subject_reduction subject_reduction_from_bundle)

-- Discharge routes
export BEDC.MetaCIC (
  SubjectReductionDischargeBundle
)

theorem not_appArgTypeStable : ¬ AppArgTypeStable := by
  -- BEDC touchpoint anchor: BEDC.MetaCIC.Term BEDC.MetaCIC.Typing
  exact BEDC.MetaCIC.not_appArgTypeStable

theorem not_lamDomainSubjectReduction : ¬ LamDomainSubjectReduction := by
  -- BEDC touchpoint anchor: BEDC.MetaCIC.Term BEDC.MetaCIC.Typing
  exact BEDC.MetaCIC.not_lamDomainSubjectReduction

theorem not_piDomainSubjectReduction : ¬ PiDomainSubjectReduction := by
  -- BEDC touchpoint anchor: BEDC.MetaCIC.Term BEDC.MetaCIC.Typing
  exact BEDC.MetaCIC.not_piDomainSubjectReduction

theorem not_subjectReductionDischargeBundle :
    ¬ SubjectReductionDischargeBundle := by
  -- BEDC touchpoint anchor: BEDC.MetaCIC.Term BEDC.MetaCIC.Typing
  exact BEDC.MetaCIC.not_subjectReductionDischargeBundle

-- Closed term operations
export BEDC.MetaCIC (shift_closed substitute_closed)

-- Closure preservation
export BEDC.MetaCIC (
  betaStep_preserves_closed
  betaStarStep_preserves_closed
  substitute_var_preserves_closed_at
  substitute_preserves_closed_at
  shift_one_preserves_closed_succ
)

-- Partial subject reduction discharge
export BEDC.MetaCIC (subject_reduction_beta_sort_var)

-- Counter-witnesses
export BEDC.MetaCIC (subject_reduction_closed_app_independent_codomain subject_reduction_closed_app_counterexample)

end BEDC.MetaCIC.Audit
