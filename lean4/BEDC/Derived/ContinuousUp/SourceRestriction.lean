import BEDC.Derived.ContinuousUp.Transport

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuousFunctionCarrier_empty_source_restriction_modulus_chain
    {restricted source map target oldMod oldCert delta1 delta2 delta cert : BHist} :
    Cont restricted BHist.Empty source ->
      ContinuousFunctionCarrier source map target oldMod oldCert ->
        ContinuousModulusChain target delta1 delta2 cert ->
          Cont delta1 delta2 delta ->
            ContinuousFunctionCarrier restricted map target delta cert ∧
              ContinuousModulusWitness target delta cert := by
  intro sourceRestriction carrier chain compositeRel
  have replaced :
      ContinuousFunctionCarrier source map target delta cert :=
    ContinuousFunctionCarrier_modulus_chain_replacement carrier chain compositeRel
  have sameSource : hsame source restricted :=
    sourceRestriction
  have restrictedCarrier :
      ContinuousFunctionCarrier restricted map target delta cert :=
    ContinuousFunctionCarrier_hsame_transport sameSource (hsame_refl map) (hsame_refl target)
      (hsame_refl delta) (hsame_refl cert) replaced
  have modulusWitness : ContinuousModulusWitness target delta cert :=
    ContinuousModulusChain_composite_closed chain compositeRel
  exact And.intro restrictedCarrier modulusWitness

theorem ContinuousFunctionCarrier_empty_source_restriction_public_readback
    {restricted source map target target' oldMod oldCert delta1 delta2 delta cert cert' : BHist} :
    Cont restricted BHist.Empty source ->
      ContinuousFunctionCarrier source map target oldMod oldCert ->
        ContinuousModulusChain target delta1 delta2 cert ->
          Cont delta1 delta2 delta ->
            ContinuousFunctionCarrier restricted map target' delta cert' ->
              hsame target target' ∧ hsame cert cert' := by
  intro sourceRestriction carrier chain compositeRel displayed
  have restrictedCarrier :
      ContinuousFunctionCarrier restricted map target delta cert :=
    (ContinuousFunctionCarrier_empty_source_restriction_modulus_chain sourceRestriction carrier
      chain compositeRel).left
  exact ContinuousFunctionCarrier_target_cert_deterministic restrictedCarrier displayed

end BEDC.Derived.ContinuousUp
