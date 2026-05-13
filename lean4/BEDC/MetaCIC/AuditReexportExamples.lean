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

/-- Setup route reference: the typeclass-mediated subject-reduction theorem is exported. -/
example [SubjectReductionSetup]
    {ctx : Ctx} {t t' A : Term}
    (ht : HasType ctx t A) (hbeta : BetaStep t t') :
    HasType ctx t' A :=
  subject_reduction_via_setup ht hbeta

/-- Obstruction marker reference: the audit namespace exports the consistency obstruction. -/
example : ¬ closed_consistency_reduction_obstruction :=
  closed_consistency_reduction_obstruction_not_available

end BEDC.MetaCIC.AuditExamples
