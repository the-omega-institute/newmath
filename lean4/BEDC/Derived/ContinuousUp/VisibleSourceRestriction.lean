import BEDC.Derived.ContinuousUp.SourceRestriction
import BEDC.Derived.ContinuousUp.Suffix

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuousFunctionCarrier_visible_empty_source_restriction_terminal_modulus_commutes
    {p q restricted source map target modulus cert extra modulus' cert' displayedTarget
      displayedCert : BHist} :
    Cont restricted BHist.Empty source ->
      ContinuousFunctionCarrier (append p source) map (append p target) (append modulus q)
        (append (append p cert) q) ->
        ContinuousModulusWitness cert extra cert' -> Cont modulus extra modulus' ->
          ContinuousFunctionCarrier (append p restricted) map (append p displayedTarget)
            (append modulus' q) (append (append p displayedCert) q) ->
            hsame target displayedTarget ∧ hsame cert' displayedCert := by
  intro sourceRestriction visibleCarrier terminalWitness modulusRel displayedCarrier
  have carrierData :=
    (ContinuousFunctionCarrier_visible_modulus_context_iff (p := p) (q := q)
      (source := source) (map := map) (target := target) (modulus := modulus)
      (cert := cert)).mp visibleCarrier
  have displayedData :=
    (ContinuousFunctionCarrier_visible_modulus_context_iff (p := p) (q := q)
      (source := restricted) (map := map) (target := displayedTarget) (modulus := modulus')
      (cert := displayedCert)).mp displayedCarrier
  exact
    ContinuousFunctionCarrier_empty_source_restriction_terminal_modulus_commutes
      sourceRestriction carrierData.right.right terminalWitness modulusRel displayedData.right.right

theorem ContinuousFunctionCarrier_visible_source_restriction_terminal_modulus_normal_form
    {p q restricted source map target target' modulus0 cert0 extra1 modulus1 cert1 extra2
      modulus2 cert2 extra3 modulus3 cert3 extra12 modulus12 extra123 modulus123 cert' :
      BHist} :
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
      ContinuousFunctionCarrier (append p restricted) map (append p target')
        (append modulus3 q) (append (append p cert') q) ->
      ContinuousFunctionCarrier (append p restricted) map (append p target)
        (append modulus123 q) (append (append p cert3) q) ∧
        hsame target target' ∧ hsame cert3 cert' ∧ hsame modulus3 modulus123 := by
  intro sourceRestriction carrier witness1 witness2 witness3 rel1 rel2 rel3 rel12
    relMod12 rel123 relMod123 displayed
  have visibleData :=
    (ContinuousFunctionCarrier_visible_modulus_context_iff (p := p) (q := q)
      (source := source) (map := map) (target := target) (modulus := modulus0)
      (cert := cert0)).mp carrier
  have sequential2 :
      ContinuousFunctionCarrier (append p source) map (append p target)
        (append modulus2 q) (append (append p cert2) q) :=
    ContinuousFunctionCarrier_visible_terminal_modulus_extension_transitive
      carrier witness1 rel1 witness2 rel2
  have reassoc12 :
      ContinuousFunctionCarrier (append p source) map (append p target)
        (append modulus12 q) (append (append p cert2) q) ∧
        hsame modulus2 modulus12 := by
    have reassoc :=
      ContinuousFunctionCarrier_visible_terminal_modulus_reassociation
        carrier witness1 witness2 rel1 rel2 rel12 relMod12
    exact And.intro reassoc.right.left reassoc.right.right
  have relMod12Extra3 : Cont modulus12 extra3 modulus123 := by
    cases relMod12
    cases rel123
    cases relMod123
    exact (append_assoc modulus0 extra12 extra3).symm
  have reassociated :
      ContinuousFunctionCarrier (append p source) map (append p target)
        (append modulus123 q) (append (append p cert3) q) :=
    ContinuousFunctionCarrier_visible_terminal_modulus_extension
      reassoc12.left witness3 relMod12Extra3
  have sameModulus3Modulus123 : hsame modulus3 modulus123 := by
    cases rel1
    cases rel2
    cases rel3
    cases rel12
    cases rel123
    cases relMod123
    exact
      (congrArg (fun history => append history extra3)
        (append_assoc modulus0 extra1 extra2)).trans
        (append_assoc modulus0 (append extra1 extra2) extra3)
  have centralReassociated :=
    (ContinuousFunctionCarrier_visible_modulus_context_iff (p := p) (q := q)
      (source := source) (map := map) (target := target) (modulus := modulus123)
      (cert := cert3)).mp reassociated
  have sameSource : hsame source restricted := sourceRestriction
  have restrictedCentral :
      ContinuousFunctionCarrier restricted map target modulus123 cert3 :=
    ContinuousFunctionCarrier_hsame_transport sameSource (hsame_refl map) (hsame_refl target)
      (hsame_refl modulus123) (hsame_refl cert3) centralReassociated.right.right
  have restrictedVisible :
      ContinuousFunctionCarrier (append p restricted) map (append p target)
        (append modulus123 q) (append (append p cert3) q) :=
    (ContinuousFunctionCarrier_visible_modulus_context_iff (p := p) (q := q)
      (source := restricted) (map := map) (target := target) (modulus := modulus123)
      (cert := cert3)).mpr
      (And.intro visibleData.left (And.intro visibleData.right.left restrictedCentral))
  have sequentialRestricted :
      ContinuousFunctionCarrier (append p restricted) map (append p target)
        (append modulus3 q) (append (append p cert3) q) := by
    have sequential3 :
        ContinuousFunctionCarrier (append p source) map (append p target)
          (append modulus3 q) (append (append p cert3) q) :=
      ContinuousFunctionCarrier_visible_terminal_modulus_extension sequential2 witness3 rel3
    have centralSequential :=
      (ContinuousFunctionCarrier_visible_modulus_context_iff (p := p) (q := q)
        (source := source) (map := map) (target := target) (modulus := modulus3)
        (cert := cert3)).mp sequential3
    have restrictedSequentialCentral :
        ContinuousFunctionCarrier restricted map target modulus3 cert3 :=
      ContinuousFunctionCarrier_hsame_transport sameSource (hsame_refl map)
        (hsame_refl target) (hsame_refl modulus3) (hsame_refl cert3)
        centralSequential.right.right
    exact
      (ContinuousFunctionCarrier_visible_modulus_context_iff (p := p) (q := q)
        (source := restricted) (map := map) (target := target) (modulus := modulus3)
        (cert := cert3)).mpr
        (And.intro visibleData.left
          (And.intro visibleData.right.left restrictedSequentialCentral))
  have readback :
      hsame target target' ∧ hsame cert3 cert' :=
    ContinuousFunctionCarrier_visible_modulus_context_target_cert_deterministic
      sequentialRestricted displayed
  exact And.intro restrictedVisible
    (And.intro readback.left (And.intro readback.right sameModulus3Modulus123))

end BEDC.Derived.ContinuousUp
