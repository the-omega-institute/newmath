import BEDC.MetaCIC.Consistency
import BEDC.MetaCIC.SubjectReduction
import BEDC.MetaCIC.SubjectReduction.DischargeBundle
import BEDC.MetaCIC.SubjectReduction.SetupClass
import BEDC.MetaCIC.ClosedTerm
import BEDC.MetaCIC.Normalization

namespace BEDC.MetaCIC.Audit

/-! ## Re-exports of MetaCIC audit theorems

This module re-exports the BEDC.MetaCIC audit-relevant theorems
in a single namespace for downstream consumers. -/

-- Consistency
export BEDC.MetaCIC (no_closed_normal_proof_of_false closed_normal_consistency_assembly closed_consistency_reduction_obstruction_not_available)

-- Subject reduction
export BEDC.MetaCIC (subject_reduction subject_reduction_from_bundle subject_reduction_via_setup)

-- Discharge routes
export BEDC.MetaCIC (SubjectReductionDischargeBundle SubjectReductionSetup)

-- Closed term operations
export BEDC.MetaCIC (shift_closed substitute_closed)

-- Counter-witnesses
export BEDC.MetaCIC (subject_reduction_closed_app_independent_codomain subject_reduction_closed_app_counterexample)

end BEDC.MetaCIC.Audit
