import BEDC.Derived.ContinuousUp.TerminalModulusExtension
import BEDC.Derived.ContinuousUp.Transport

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

def ContinuousPatternSpec
    (source f middle g target fg modF modG modFG certF certG cert : BHist) : Prop :=
  ContinuousFunctionCarrier source f middle modF certF ∧
    ContinuousFunctionCarrier middle g target modG certG ∧
      Cont f g fg ∧ Cont modF modG modFG ∧ Cont target modFG cert

theorem ContinuousPatternSpec_comp_carrier
    {source f middle g target fg modF modG modFG certF certG cert : BHist} :
    ContinuousPatternSpec source f middle g target fg modF modG modFG certF certG cert ->
      ContinuousFunctionCarrier source fg target modFG cert := by
  intro spec
  exact
    ContinuousFunctionCarrier_comp_closed spec.left spec.right.left spec.right.right.left
      spec.right.right.right.left spec.right.right.right.right

def ContinuousClassifierSpec
    (source source' map map' target target' modulus modulus' cert cert' : BHist) : Prop :=
  ContinuousFunctionCarrier source map target modulus cert ∧
    ContinuousFunctionCarrier source' map' target' modulus' cert' ∧
      hsame source source' ∧ hsame map map' ∧ hsame modulus modulus'

theorem ContinuousClassifierSpec_target_cert_readback
    {source source' map map' target target' modulus modulus' cert cert' : BHist} :
    ContinuousClassifierSpec source source' map map' target target' modulus modulus' cert cert' ->
      hsame target target' ∧ hsame cert cert' := by
  intro spec
  have transported :
      ContinuousFunctionCarrier source map target' modulus cert' :=
    ContinuousFunctionCarrier_hsame_transport
      (hsame_symm spec.right.right.left)
      (hsame_symm spec.right.right.right.left)
      (hsame_refl target')
      (hsame_symm spec.right.right.right.right)
      (hsame_refl cert')
      spec.right.left
  exact ContinuousFunctionCarrier_target_cert_deterministic spec.left transported

theorem ContinuousFunctionCarrier_stability_certificate_fields :
    (forall {h : BHist}, hsame h h) ∧
    (forall {h k : BHist}, hsame h k -> hsame k h) ∧
    (forall {h k r : BHist}, hsame h k -> hsame k r -> hsame h r) ∧
    (forall {source map target modulus cert source' map' target' modulus' cert' : BHist},
      hsame source source' -> hsame map map' -> hsame target target' ->
        hsame modulus modulus' -> hsame cert cert' ->
          ContinuousFunctionCarrier source map target modulus cert ->
            ContinuousFunctionCarrier source' map' target' modulus' cert') ∧
    (forall {source modulus cert : BHist}, ContinuousModulusWitness source modulus cert ->
      ContinuousFunctionCarrier source BHist.Empty source modulus cert) ∧
    (forall {source middle target f g fg modF modG modFG certF certG cert : BHist},
      ContinuousFunctionCarrier source f middle modF certF ->
        ContinuousFunctionCarrier middle g target modG certG ->
          Cont f g fg -> Cont modF modG modFG -> Cont target modFG cert ->
            ContinuousFunctionCarrier source fg target modFG cert) := by
  exact And.intro
    (fun {h : BHist} => hsame_refl h)
    (And.intro
      (fun {h k : BHist} same => hsame_symm same)
      (And.intro
        (fun {h k r : BHist} sameHK sameKR => hsame_trans sameHK sameKR)
        (And.intro
          (fun {source map target modulus cert source' map' target' modulus' cert' : BHist}
              sameSource sameMap sameTarget sameModulus sameCert carrier =>
            ContinuousFunctionCarrier_hsame_transport sameSource sameMap sameTarget sameModulus
              sameCert carrier)
          (And.intro
            (fun {source modulus cert : BHist} witness =>
              ContinuousFunctionCarrier_empty_map_identity witness)
            (fun {source middle target f g fg modF modG modFG certF certG cert : BHist}
                first second mapRel modulusRel certRel =>
              ContinuousFunctionCarrier_comp_closed first second mapRel modulusRel certRel)))))

theorem ContinuousFunctionCarrier_ledger_policy_fields :
    (forall {source map target oldMod oldCert delta1 delta2 delta cert : BHist},
      ContinuousFunctionCarrier source map target oldMod oldCert ->
        ContinuousModulusChain target delta1 delta2 cert -> Cont delta1 delta2 delta ->
          ContinuousFunctionCarrier source map target delta cert) ∧
    (forall {source map target modulus cert extra modulus' cert' : BHist},
      ContinuousFunctionCarrier source map target modulus cert ->
        ContinuousModulusWitness cert extra cert' -> Cont modulus extra modulus' ->
          ContinuousFunctionCarrier source map target modulus' cert') := by
  exact And.intro
    (fun {source map target oldMod oldCert delta1 delta2 delta cert : BHist}
        carrier chain compositeRel =>
      ContinuousFunctionCarrier_modulus_chain_replacement carrier chain compositeRel)
    (fun {source map target modulus cert extra modulus' cert' : BHist}
        carrier terminalWitness modulusRel =>
      ContinuousFunctionCarrier_terminal_modulus_extension carrier terminalWitness modulusRel)

end BEDC.Derived.ContinuousUp
