import BEDC.MetaCIC.SubjectReduction
import BEDC.MetaCIC.SubjectReduction.DischargeBundle

namespace BEDC.MetaCIC

/-- Typeclass-level discharge route for subject reduction.
    A carrier substrate provides an instance by supplying the four
    discharge hypotheses; the resulting subject reduction theorem
    is then unconditional for that substrate. -/
class SubjectReductionSetup : Prop where
  betaSubst : BetaSubstitutionPreservation
  appArg : AppArgTypeStable
  lamDom : LamDomainSubjectReduction
  piDom : PiDomainSubjectReduction

/-- A `SubjectReductionSetup` instance canonically yields the
    `SubjectReductionDischargeBundle` for use with bundle-based theorems. -/
def SubjectReductionSetup.toBundle [h : SubjectReductionSetup] :
    SubjectReductionDischargeBundle where
  betaSubstitutionPreservation := h.betaSubst
  appArgTypeStable := h.appArg
  lamDomain := h.lamDom
  piDomain := h.piDom

/-- Subject reduction as an unconditional theorem when the substrate provides
    `SubjectReductionSetup`. -/
theorem subject_reduction_via_setup [h : SubjectReductionSetup]
    {Γ : Ctx} {t t' A : Term}
    (ht : HasType Γ t A) (hbeta : BetaStep t t') :
    HasType Γ t' A :=
  subject_reduction_from_bundle (h := SubjectReductionSetup.toBundle) ht hbeta

end BEDC.MetaCIC
