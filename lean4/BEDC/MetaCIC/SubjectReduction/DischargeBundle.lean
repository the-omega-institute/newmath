import BEDC.MetaCIC.SubjectReduction

namespace BEDC.MetaCIC

/-- Bundle of the four discharge hypotheses needed to make subject reduction
    unconditional on the substrate. Each field is a substrate-internal Prop
    that must be discharged to lift the parameterised subject_reduction to
    an unconditional theorem. -/
structure SubjectReductionDischargeBundle : Prop where
  betaSubstitutionPreservation : BetaSubstitutionPreservation
  appArgTypeStable : AppArgTypeStable
  lamDomain : LamDomainSubjectReduction
  piDomain : PiDomainSubjectReduction

/-- Subject reduction as an unconditional theorem when the discharge bundle is supplied. -/
theorem subject_reduction_from_bundle
    (h : SubjectReductionDischargeBundle)
    {Γ : Ctx} {t t' A : Term}
    (ht : HasType Γ t A) (hbeta : BetaStep t t') :
    HasType Γ t' A :=
  subject_reduction h.betaSubstitutionPreservation h.appArgTypeStable
    h.lamDomain h.piDomain ht hbeta

end BEDC.MetaCIC
