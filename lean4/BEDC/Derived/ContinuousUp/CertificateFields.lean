import BEDC.Derived.ContinuousUp.TerminalModulusExtension
import BEDC.Derived.ContinuousUp.Transport

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

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
