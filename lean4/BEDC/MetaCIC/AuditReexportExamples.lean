import BEDC.MetaCIC.AuditReexport

namespace BEDC.MetaCIC.AuditExamples

open BEDC.MetaCIC.Audit

/-- Direct reference: the audit theorem is available without its original namespace path. -/
example : NoClosedNormalProofOfFalseStatement :=
  no_closed_normal_proof_of_false

/-- Bundle type reference: the audit namespace exports the bundle type as first-class. -/
example (h : SubjectReductionDischargeBundle) :
    SubjectReductionDischargeBundle :=
  h

/-- Bundle route reference: explicit discharge evidence feeds subject reduction. -/
example (h : SubjectReductionDischargeBundle)
    {ctx : Ctx} {t t' A : Term}
    (ht : HasType ctx t A) (hbeta : BetaStep t t') :
    HasType ctx t' A :=
  subject_reduction_from_bundle h ht hbeta

/-- Obstruction reference: the audit namespace exports the checked no-bundle fact. -/
example : ¬ SubjectReductionDischargeBundle :=
  not_subjectReductionDischargeBundle

/-- Obstruction marker reference: the audit namespace exports the consistency obstruction. -/
example : ¬ closed_consistency_reduction_obstruction :=
  closed_consistency_reduction_obstruction_not_available

end BEDC.MetaCIC.AuditExamples
