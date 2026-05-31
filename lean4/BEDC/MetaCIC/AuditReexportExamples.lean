import BEDC.MetaCIC.AuditReexport

namespace BEDC.MetaCIC.AuditExamples

open BEDC.MetaCIC.Audit

example : NoClosedNormalProofOfFalseStatement :=
  no_closed_normal_proof_of_false

example (h : SubjectReductionDischargeBundle) :
    SubjectReductionDischargeBundle :=
  h

example (h : SubjectReductionDischargeBundle)
    {ctx : Ctx} {t t' A : Term}
    (ht : HasType ctx t A) (hbeta : BetaStep t t') :
    HasType ctx t' A :=
  subject_reduction_from_bundle h ht hbeta

example : ¬ SubjectReductionDischargeBundle :=
  not_subjectReductionDischargeBundle

example : ¬ AppArgTypeStable :=
  BEDC.MetaCIC.Audit.not_appArgTypeStable

example : ¬ LamDomainSubjectReduction :=
  BEDC.MetaCIC.Audit.not_lamDomainSubjectReduction

example : ¬ PiDomainSubjectReduction :=
  BEDC.MetaCIC.Audit.not_piDomainSubjectReduction

example : ¬ closed_consistency_reduction_obstruction :=
  closed_consistency_reduction_obstruction_not_available

end BEDC.MetaCIC.AuditExamples
