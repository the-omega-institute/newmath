import BEDC.Derived.ContinuousUp.Suffix
import BEDC.Derived.ContinuousUp.TerminalModulusExtension

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ContinuousFunctionCarrier_visible_terminal_modulus_extension
    {p q source map target modulus cert extra modulus' cert' : BHist} :
    ContinuousFunctionCarrier (append p source) map (append p target) (append modulus q)
        (append (append p cert) q) ->
      ContinuousModulusWitness cert extra cert' ->
        Cont modulus extra modulus' ->
          ContinuousFunctionCarrier (append p source) map (append p target)
            (append modulus' q) (append (append p cert') q) := by
  intro carrier terminalWitness modulusRel
  have visibleData :=
    (ContinuousFunctionCarrier_visible_modulus_context_iff (p := p) (q := q)
      (source := source) (map := map) (target := target) (modulus := modulus)
      (cert := cert)).mp carrier
  have central :
      ContinuousFunctionCarrier source map target modulus' cert' :=
    ContinuousFunctionCarrier_terminal_modulus_extension visibleData.right.right
      terminalWitness modulusRel
  exact
    (ContinuousFunctionCarrier_visible_modulus_context_iff (p := p) (q := q)
      (source := source) (map := map) (target := target) (modulus := modulus')
      (cert := cert')).mpr
      (And.intro visibleData.left (And.intro visibleData.right.left central))

theorem ContinuousFunctionCarrier_visible_terminal_modulus_extension_output_determinacy
    {p q source map target target' modulus cert extra modulus' cert' cert'' : BHist} :
    ContinuousFunctionCarrier (append p source) map (append p target) (append modulus q)
        (append (append p cert) q) ->
      ContinuousModulusWitness cert extra cert' ->
        Cont modulus extra modulus' ->
          ContinuousFunctionCarrier (append p source) map (append p target')
              (append modulus' q) (append (append p cert'') q) ->
            hsame target target' ∧ hsame cert' cert'' := by
  intro carrier terminalWitness modulusRel displayed
  have canonical :
      ContinuousFunctionCarrier (append p source) map (append p target)
        (append modulus' q) (append (append p cert') q) :=
    ContinuousFunctionCarrier_visible_terminal_modulus_extension carrier terminalWitness modulusRel
  exact ContinuousFunctionCarrier_visible_modulus_context_target_cert_deterministic canonical displayed

theorem ContinuousFunctionCarrier_visible_terminal_modulus_extension_transitive
    {p q source map target modulus0 cert0 extra1 modulus1 cert1 extra2 modulus2 cert2 :
      BHist} :
    ContinuousFunctionCarrier (append p source) map (append p target) (append modulus0 q)
        (append (append p cert0) q) ->
      ContinuousModulusWitness cert0 extra1 cert1 ->
        Cont modulus0 extra1 modulus1 ->
          ContinuousModulusWitness cert1 extra2 cert2 ->
            Cont modulus1 extra2 modulus2 ->
              ContinuousFunctionCarrier (append p source) map (append p target)
                (append modulus2 q) (append (append p cert2) q) := by
  intro carrier witness1 rel1 witness2 rel2
  exact ContinuousFunctionCarrier_visible_terminal_modulus_extension
    (ContinuousFunctionCarrier_visible_terminal_modulus_extension carrier witness1 rel1)
    witness2 rel2

theorem ContinuousFunctionCarrier_visible_terminal_modulus_reassociation
    {p q source map target modulus0 cert0 extra1 modulus1 cert1 extra2 extra12 modulus2
      modulus12 cert2 : BHist} :
    ContinuousFunctionCarrier (append p source) map (append p target) (append modulus0 q)
        (append (append p cert0) q) ->
      ContinuousModulusWitness cert0 extra1 cert1 ->
        ContinuousModulusWitness cert1 extra2 cert2 ->
          Cont modulus0 extra1 modulus1 ->
            Cont modulus1 extra2 modulus2 ->
              Cont extra1 extra2 extra12 ->
                Cont modulus0 extra12 modulus12 ->
                  ContinuousFunctionCarrier (append p source) map (append p target)
                      (append modulus2 q) (append (append p cert2) q) ∧
                    ContinuousFunctionCarrier (append p source) map (append p target)
                      (append modulus12 q) (append (append p cert2) q) ∧
                    hsame modulus2 modulus12 := by
  intro carrier witness1 witness2 rel1 rel2 extraRel compositeRel
  have sequential :
      ContinuousFunctionCarrier (append p source) map (append p target) (append modulus2 q)
        (append (append p cert2) q) :=
    ContinuousFunctionCarrier_visible_terminal_modulus_extension_transitive
      carrier witness1 rel1 witness2 rel2
  have chain : ContinuousModulusChain cert0 extra1 extra2 cert2 := by
    cases witness1 with
    | intro cert0Carrier witness1Rest =>
        cases witness1Rest with
        | intro extra1Carrier witness1Rest =>
            cases witness1Rest with
            | intro cert1Carrier cert0Extra1 =>
                cases witness2 with
                | intro _cert1Carrier witness2Rest =>
                    cases witness2Rest with
                    | intro extra2Carrier witness2Rest =>
                        cases witness2Rest with
                        | intro cert2Carrier cert1Extra2 =>
                            exact
                              And.intro cert0Carrier
                                (And.intro extra1Carrier
                                  (And.intro extra2Carrier
                                    (And.intro cert2Carrier
                                      (Exists.intro cert1
                                        (And.intro cert0Extra1 cert1Extra2)))))
  have compositeWitness : ContinuousModulusWitness cert0 extra12 cert2 :=
    ContinuousModulusChain_composite_closed chain extraRel
  have composite :
      ContinuousFunctionCarrier (append p source) map (append p target) (append modulus12 q)
        (append (append p cert2) q) :=
    ContinuousFunctionCarrier_visible_terminal_modulus_extension carrier compositeWitness compositeRel
  have sameModulus : hsame modulus2 modulus12 :=
    cont_assoc_hsame rel1 rel2 extraRel compositeRel
  exact And.intro sequential (And.intro composite sameModulus)

theorem ContinuousFunctionCarrier_visible_terminal_modulus_reassociation_output_determinacy
    {p q source map target target' modulus0 cert0 extra1 modulus1 cert1 extra2 extra12
      modulus2 modulus12 cert2 cert'' : BHist} :
    ContinuousFunctionCarrier (append p source) map (append p target) (append modulus0 q)
        (append (append p cert0) q) ->
      ContinuousModulusWitness cert0 extra1 cert1 ->
        ContinuousModulusWitness cert1 extra2 cert2 ->
          Cont modulus0 extra1 modulus1 ->
            Cont modulus1 extra2 modulus2 ->
              Cont extra1 extra2 extra12 ->
                Cont modulus0 extra12 modulus12 ->
                  ContinuousFunctionCarrier (append p source) map (append p target')
                      (append modulus12 q) (append (append p cert'') q) ->
                    hsame target target' ∧ hsame cert2 cert'' ∧
                      hsame modulus2 modulus12 := by
  intro carrier witness1 witness2 rel1 rel2 relExtra relComposite displayed
  have canonical :=
    ContinuousFunctionCarrier_visible_terminal_modulus_reassociation
      carrier witness1 witness2 rel1 rel2 relExtra relComposite
  have targetCert :=
    ContinuousFunctionCarrier_visible_modulus_context_target_cert_deterministic
      canonical.right.left displayed
  exact And.intro targetCert.left (And.intro targetCert.right canonical.right.right)

end BEDC.Derived.ContinuousUp
