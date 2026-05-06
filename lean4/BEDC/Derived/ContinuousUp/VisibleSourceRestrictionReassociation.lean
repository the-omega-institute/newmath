import BEDC.Derived.ContinuousUp.VisibleSourceRestriction

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuousFunctionCarrier_visible_source_restriction_terminal_modulus_reassociation
    {p q restricted source map target modulus0 cert0 extra1 modulus1 cert1 extra2 modulus2
      cert2 extra3 modulus3 cert3 extra12 modulus12 extra123 modulus123 : BHist} :
    Cont restricted BHist.Empty source ->
      ContinuousFunctionCarrier (append p source) map (append p target) (append modulus0 q)
          (append (append p cert0) q) ->
        ContinuousModulusWitness cert0 extra1 cert1 ->
          ContinuousModulusWitness cert1 extra2 cert2 ->
            ContinuousModulusWitness cert2 extra3 cert3 ->
              Cont modulus0 extra1 modulus1 ->
                Cont modulus1 extra2 modulus2 ->
                  Cont modulus2 extra3 modulus3 ->
                    Cont extra1 extra2 extra12 ->
                      Cont modulus0 extra12 modulus12 ->
                        Cont extra12 extra3 extra123 ->
                          Cont modulus0 extra123 modulus123 ->
                            ContinuousFunctionCarrier (append p restricted) map
                                (append p target) (append modulus3 q)
                                (append (append p cert3) q) ∧
                              ContinuousFunctionCarrier (append p restricted) map
                                  (append p target) (append modulus123 q)
                                  (append (append p cert3) q) ∧
                                hsame modulus3 modulus123 := by
  intro sourceRestriction carrier witness1 witness2 witness3 rel1 rel2 rel3 rel12
    relMod12 rel123 relMod123
  have sequentialOverSource :
      ContinuousFunctionCarrier (append p source) map (append p target)
        (append modulus2 q) (append (append p cert2) q) :=
    ContinuousFunctionCarrier_visible_terminal_modulus_extension_transitive carrier witness1
      rel1 witness2 rel2
  have sequentialVisible :
      ContinuousFunctionCarrier (append p restricted) map (append p target)
        (append modulus3 q) (append (append p cert3) q) := by
    have overSource :
        ContinuousFunctionCarrier (append p source) map (append p target)
          (append modulus3 q) (append (append p cert3) q) :=
      ContinuousFunctionCarrier_visible_terminal_modulus_extension sequentialOverSource witness3
        rel3
    have visibleData :=
      (ContinuousFunctionCarrier_visible_modulus_context_iff (p := p) (q := q)
        (source := source) (map := map) (target := target) (modulus := modulus3)
        (cert := cert3)).mp overSource
    have restrictedCentral :
        ContinuousFunctionCarrier restricted map target modulus3 cert3 :=
      ContinuousFunctionCarrier_hsame_transport sourceRestriction (hsame_refl map)
        (hsame_refl target) (hsame_refl modulus3) (hsame_refl cert3)
        visibleData.right.right
    exact
      (ContinuousFunctionCarrier_visible_modulus_context_iff (p := p) (q := q)
        (source := restricted) (map := map) (target := target) (modulus := modulus3)
        (cert := cert3)).mpr
        (And.intro visibleData.left (And.intro visibleData.right.left restrictedCentral))
  have normalForm :=
    ContinuousFunctionCarrier_visible_source_restriction_terminal_modulus_normal_form
      sourceRestriction carrier witness1 witness2 witness3 rel1 rel2 rel3 rel12 relMod12
      rel123 relMod123 sequentialVisible
  exact And.intro sequentialVisible (And.intro normalForm.left normalForm.right.right.right)

end BEDC.Derived.ContinuousUp
