import BEDC.Derived.ContinuousUp.Transport
import BEDC.Derived.ContinuousUp.TerminalModulusExtension
import BEDC.Derived.ContinuousUp.Suffix
import BEDC.Derived.ContinuousUp.VisibleTerminalModulusExtension

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

theorem ContinuousFunctionCarrier_empty_source_restriction_public_package
    {restricted source map target target' oldMod oldCert delta1 delta2 delta cert cert' : BHist} :
    Cont restricted BHist.Empty source ->
      ContinuousFunctionCarrier source map target oldMod oldCert ->
        ContinuousModulusChain target delta1 delta2 cert ->
          Cont delta1 delta2 delta ->
            ContinuousFunctionCarrier restricted map target' delta cert' ->
              ContinuousFunctionCarrier restricted map target delta cert ∧
                ContinuousModulusWitness target delta cert ∧
                  hsame target target' ∧ hsame cert cert' := by
  intro sourceRestriction carrier chain compositeRel displayed
  have packaged :=
    ContinuousFunctionCarrier_empty_source_restriction_modulus_chain sourceRestriction carrier
      chain compositeRel
  have readback : hsame target target' ∧ hsame cert cert' :=
    ContinuousFunctionCarrier_target_cert_deterministic packaged.left displayed
  exact And.intro packaged.left (And.intro packaged.right readback)

theorem ContinuousFunctionCarrier_empty_source_restriction_transitive_package
    {v u source map target oldMod oldCert delta1 delta2 delta cert displayedTarget
      displayedCert : BHist} :
    Cont v BHist.Empty u ->
      Cont u BHist.Empty source ->
        ContinuousFunctionCarrier source map target oldMod oldCert ->
          ContinuousModulusChain target delta1 delta2 cert ->
            Cont delta1 delta2 delta ->
              ContinuousFunctionCarrier v map displayedTarget delta displayedCert ->
                ContinuousFunctionCarrier v map target delta cert ∧
                  ContinuousModulusWitness target delta cert ∧
                    hsame target displayedTarget ∧ hsame cert displayedCert := by
  intro firstRestriction secondRestriction carrier chain compositeRel displayed
  have directRestriction : Cont v BHist.Empty source :=
    secondRestriction.trans firstRestriction
  have packaged :=
    ContinuousFunctionCarrier_empty_source_restriction_modulus_chain directRestriction
      carrier chain compositeRel
  have readback :=
    ContinuousFunctionCarrier_target_cert_deterministic packaged.left displayed
  exact And.intro packaged.left (And.intro packaged.right readback)

theorem ContinuousFunctionCarrier_empty_source_restriction_functorial_action
    {source map target oldMod oldCert delta1 delta2 delta cert displayedTarget displayedCert v u
      displayedTarget2 displayedCert2 : BHist} :
    ContinuousFunctionCarrier source map target oldMod oldCert ->
      ContinuousModulusChain target delta1 delta2 cert ->
        Cont delta1 delta2 delta ->
          ContinuousFunctionCarrier source map displayedTarget delta displayedCert ->
            (ContinuousFunctionCarrier source map target delta cert ∧
                ContinuousModulusWitness target delta cert ∧
                  hsame target displayedTarget ∧ hsame cert displayedCert) ∧
              (Cont v BHist.Empty u ->
                Cont u BHist.Empty source ->
                  ContinuousFunctionCarrier v map displayedTarget2 delta displayedCert2 ->
                    ContinuousFunctionCarrier v map target delta cert ∧
                      ContinuousModulusWitness target delta cert ∧
                        hsame target displayedTarget2 ∧ hsame cert displayedCert2) := by
  intro carrier chain compositeRel displayed
  have identityPackage :
      ContinuousFunctionCarrier source map target delta cert ∧
        ContinuousModulusWitness target delta cert ∧
          hsame target displayedTarget ∧ hsame cert displayedCert :=
    by
      have packaged :=
        ContinuousFunctionCarrier_empty_source_restriction_modulus_chain
          (cont_right_unit source) carrier chain compositeRel
      exact And.intro packaged.left
        (And.intro packaged.right
          (ContinuousFunctionCarrier_target_cert_deterministic packaged.left displayed))
  constructor
  · exact identityPackage
  · intro firstRestriction secondRestriction displayed2
    exact ContinuousFunctionCarrier_empty_source_restriction_transitive_package
      firstRestriction secondRestriction carrier chain compositeRel displayed2

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

theorem ContinuousFunctionCarrier_empty_source_restriction_terminal_modulus_package
    {restricted source map target modulus cert extra modulus' cert' displayedTarget displayedCert :
      BHist} :
    Cont restricted BHist.Empty source ->
      ContinuousFunctionCarrier source map target modulus cert ->
        ContinuousModulusWitness cert extra cert' ->
          Cont modulus extra modulus' ->
            ContinuousFunctionCarrier restricted map displayedTarget modulus' displayedCert ->
              ContinuousFunctionCarrier restricted map target modulus' cert' ∧
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
  exact And.intro restrictedCarrier
    (ContinuousFunctionCarrier_target_cert_deterministic restrictedCarrier displayed)

theorem ContinuousFunctionCarrier_empty_source_restriction_visible_terminal_modulus_commutes
    {restricted p q source map target modulus cert extra modulus' cert' displayedTarget
        displayedCert : BHist} :
    Cont restricted BHist.Empty source ->
      ContinuousFunctionCarrier (append p source) map (append p target) (append modulus q)
          (append (append p cert) q) ->
        ContinuousModulusWitness cert extra cert' ->
          Cont modulus extra modulus' ->
            ContinuousFunctionCarrier (append p restricted) map displayedTarget
                (append modulus' q) displayedCert ->
              hsame (append p target) displayedTarget ∧
                hsame (append (append p cert') q) displayedCert := by
  intro sourceRestriction carrier terminalWitness modulusRel displayed
  have extended :
      ContinuousFunctionCarrier (append p source) map (append p target)
        (append modulus' q) (append (append p cert') q) :=
    ContinuousFunctionCarrier_visible_terminal_modulus_extension carrier terminalWitness modulusRel
  have sameSource : hsame (append p source) (append p restricted) := by
    cases sourceRestriction
    rfl
  have restrictedCarrier :
      ContinuousFunctionCarrier (append p restricted) map (append p target)
        (append modulus' q) (append (append p cert') q) :=
    ContinuousFunctionCarrier_hsame_transport sameSource (hsame_refl map)
      (hsame_refl (append p target)) (hsame_refl (append modulus' q))
      (hsame_refl (append (append p cert') q)) extended
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

theorem ContinuousFunctionCarrier_visible_source_restriction_terminal_modulus_commutes
    {p q restricted source map target target' modulus cert extra modulus' cert' cert'' :
      BHist} :
    Cont restricted BHist.Empty source ->
      ContinuousFunctionCarrier (append p source) map (append p target) (append modulus q)
          (append (append p cert) q) ->
        ContinuousModulusWitness cert extra cert' ->
          Cont modulus extra modulus' ->
            ContinuousFunctionCarrier (append p restricted) map (append p target')
                (append modulus' q) (append (append p cert'') q) ->
              hsame target target' ∧ hsame cert' cert'' := by
  intro sourceRestriction carrier terminalWitness modulusRel displayed
  have visibleData :=
    (ContinuousFunctionCarrier_visible_modulus_context_iff (p := p) (q := q)
      (source := source) (map := map) (target := target) (modulus := modulus)
      (cert := cert)).mp carrier
  have extended :
      ContinuousFunctionCarrier source map target modulus' cert' :=
    ContinuousFunctionCarrier_terminal_modulus_extension visibleData.right.right terminalWitness
      modulusRel
  have sameSource : hsame source restricted :=
    sourceRestriction
  have restrictedCarrier :
      ContinuousFunctionCarrier restricted map target modulus' cert' :=
    ContinuousFunctionCarrier_hsame_transport sameSource (hsame_refl map) (hsame_refl target)
      (hsame_refl modulus') (hsame_refl cert') extended
  have canonical :
      ContinuousFunctionCarrier (append p restricted) map (append p target)
        (append modulus' q) (append (append p cert') q) :=
    (ContinuousFunctionCarrier_visible_modulus_context_iff (p := p) (q := q)
      (source := restricted) (map := map) (target := target) (modulus := modulus')
      (cert := cert')).mpr
      (And.intro visibleData.left (And.intro visibleData.right.left restrictedCarrier))
  exact ContinuousFunctionCarrier_visible_modulus_context_target_cert_deterministic canonical displayed

theorem ContinuousFunctionCarrier_visible_source_restriction_modulus_chain_commutes
    {p q restricted source map target target' oldMod oldCert delta1 delta2 delta cert cert' :
      BHist} :
    Cont restricted BHist.Empty source ->
      ContinuousFunctionCarrier (append p source) map (append p target) (append oldMod q)
          (append (append p oldCert) q) ->
        ContinuousModulusChain target delta1 delta2 cert ->
          Cont delta1 delta2 delta ->
            ContinuousFunctionCarrier (append p restricted) map (append p target')
                (append delta q) (append (append p cert') q) ->
              ContinuousFunctionCarrier (append p restricted) map (append p target)
                  (append delta q) (append (append p cert) q) ∧
                ContinuousModulusWitness target delta cert ∧
                  hsame target target' ∧ hsame cert cert' := by
  intro sourceRestriction carrier chain compositeRel displayed
  have visibleData :=
    (ContinuousFunctionCarrier_visible_modulus_context_iff (p := p) (q := q)
      (source := source) (map := map) (target := target) (modulus := oldMod)
      (cert := oldCert)).mp carrier
  have centralPackage :=
    ContinuousFunctionCarrier_empty_source_restriction_modulus_chain sourceRestriction
      visibleData.right.right chain compositeRel
  have canonical :
      ContinuousFunctionCarrier (append p restricted) map (append p target)
        (append delta q) (append (append p cert) q) :=
    (ContinuousFunctionCarrier_visible_modulus_context_iff (p := p) (q := q)
      (source := restricted) (map := map) (target := target) (modulus := delta)
      (cert := cert)).mpr
      (And.intro visibleData.left (And.intro visibleData.right.left centralPackage.left))
  have readback :
      hsame target target' ∧ hsame cert cert' :=
    ContinuousFunctionCarrier_visible_modulus_context_target_cert_deterministic canonical displayed
  exact And.intro canonical (And.intro centralPackage.right readback)

theorem ContinuousFunctionCarrier_visible_source_restriction_modulus_chain_functorial_normal_form
    {p q sourceT sourceU sourceV sourceW map target targetD targetS oldMod oldCert delta1 delta2
        delta cert certD certS : BHist} :
    Cont sourceU BHist.Empty sourceT ->
      Cont sourceV BHist.Empty sourceU ->
        Cont sourceW BHist.Empty sourceV ->
          Cont sourceW BHist.Empty sourceT ->
            ContinuousFunctionCarrier (append p sourceT) map (append p target) (append oldMod q)
                (append (append p oldCert) q) ->
              ContinuousModulusChain target delta1 delta2 cert ->
                Cont delta1 delta2 delta ->
                  ContinuousFunctionCarrier (append p sourceW) map (append p targetD)
                      (append delta q) (append (append p certD) q) ->
                    ContinuousFunctionCarrier (append p sourceW) map (append p targetS)
                        (append delta q) (append (append p certS) q) ->
                      ContinuousFunctionCarrier (append p sourceW) map (append p target)
                          (append delta q) (append (append p cert) q) ∧
                        hsame target targetD ∧ hsame cert certD ∧
                          hsame target targetS ∧ hsame cert certS := by
  intro sourceUT sourceVU sourceWV sourceWT carrier chain compositeRel displayedDirect
    displayedSuccessive
  have directPackage :=
    ContinuousFunctionCarrier_visible_source_restriction_modulus_chain_commutes
      sourceWT carrier chain compositeRel displayedDirect
  have successiveRestriction : Cont sourceW BHist.Empty sourceT :=
    sourceUT.trans (sourceVU.trans sourceWV)
  have successivePackage :=
    ContinuousFunctionCarrier_visible_source_restriction_modulus_chain_commutes
      successiveRestriction carrier chain compositeRel displayedSuccessive
  exact And.intro directPackage.left
    (And.intro directPackage.right.right.left
      (And.intro directPackage.right.right.right
        (And.intro successivePackage.right.right.left successivePackage.right.right.right)))

end BEDC.Derived.ContinuousUp
