import BEDC.Derived.ContinuousUp.Transport
import BEDC.Derived.ContinuousUp.TerminalModulusExtension

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

theorem ContinuousFunctionCarrier_empty_source_restriction_terminal_modulus_commutes
    {restricted source map target modulus cert extra modulus' cert' displayedTarget displayedCert :
      BHist} :
    Cont restricted BHist.Empty source ->
      ContinuousFunctionCarrier source map target modulus cert ->
        ContinuousModulusWitness cert extra cert' ->
          Cont modulus extra modulus' ->
            ContinuousFunctionCarrier restricted map displayedTarget modulus' displayedCert ->
              hsame target displayedTarget ∧ hsame cert' displayedCert := by
  intro sourceRestriction carrier terminalWitness modulusRel displayed
  have extended :
      ContinuousFunctionCarrier source map target modulus' cert' :=
    ContinuousFunctionCarrier_terminal_modulus_extension carrier terminalWitness modulusRel
  have sameSource : hsame source restricted :=
    sourceRestriction
  have restrictedCarrier :
      ContinuousFunctionCarrier restricted map target modulus' cert' :=
    ContinuousFunctionCarrier_hsame_transport sameSource (hsame_refl map) (hsame_refl target)
      (hsame_refl modulus') (hsame_refl cert') extended
  exact ContinuousFunctionCarrier_target_cert_deterministic restrictedCarrier displayed

theorem ContinuousFunctionCarrier_empty_source_restriction_iterated_terminal_modulus_commutes
    {restricted source map target modulus cert extra0 modulus0 cert0 extra1 modulus1 cert1
      displayedTarget displayedCert : BHist} :
    Cont restricted BHist.Empty source ->
      ContinuousFunctionCarrier source map target modulus cert ->
        ContinuousModulusWitness cert extra0 cert0 ->
          Cont modulus extra0 modulus0 ->
            ContinuousModulusWitness cert0 extra1 cert1 ->
              Cont modulus0 extra1 modulus1 ->
                ContinuousFunctionCarrier restricted map displayedTarget modulus1 displayedCert ->
                  hsame target displayedTarget ∧ hsame cert1 displayedCert := by
  intro sourceRestriction carrier firstWitness firstRel secondWitness secondRel displayed
  have firstExtended :
      ContinuousFunctionCarrier source map target modulus0 cert0 :=
    ContinuousFunctionCarrier_terminal_modulus_extension carrier firstWitness firstRel
  have secondExtended :
      ContinuousFunctionCarrier source map target modulus1 cert1 :=
    ContinuousFunctionCarrier_terminal_modulus_extension firstExtended secondWitness secondRel
  have sameSource : hsame source restricted :=
    sourceRestriction
  have restrictedCarrier :
      ContinuousFunctionCarrier restricted map target modulus1 cert1 :=
    ContinuousFunctionCarrier_hsame_transport sameSource (hsame_refl map) (hsame_refl target)
      (hsame_refl modulus1) (hsame_refl cert1) secondExtended
  exact ContinuousFunctionCarrier_target_cert_deterministic restrictedCarrier displayed

end BEDC.Derived.ContinuousUp
