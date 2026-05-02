import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CategoryHomCarrier_unary_continuation_stability_law_package :
    (forall {a : BHist}, UnaryHistory a -> CategoryHomCarrier a a BHist.Empty) ∧
    (forall {a b c f g fg : BHist}, CategoryHomCarrier a b f ->
      CategoryHomCarrier b c g -> Cont f g fg -> CategoryHomCarrier a c fg) ∧
    (forall {a b c d f g h fg gh left right : BHist}, CategoryHomCarrier a b f ->
      CategoryHomCarrier b c g -> CategoryHomCarrier c d h -> Cont f g fg ->
      Cont g h gh -> Cont fg h left -> Cont f gh right ->
      CategoryHomCarrier a d left ∧ CategoryHomCarrier a d right ∧ hsame left right) ∧
    (forall {a b f left right : BHist}, CategoryHomCarrier a b f ->
      Cont BHist.Empty f left -> Cont f BHist.Empty right ->
      CategoryHomCarrier a b left ∧ CategoryHomCarrier a b right ∧ hsame left right) ∧
    (forall {a a' b b' f f' : BHist}, hsame a a' -> hsame b b' -> hsame f f' ->
      CategoryHomCarrier a b f -> CategoryHomCarrier a' b' f') ∧
    (forall {a a' b b' f g : BHist}, hsame a a' -> hsame b b' ->
      CategoryHomCarrier a b f -> CategoryHomCarrier a' b' g -> hsame f g) := by
  constructor
  · intro a carrier
    exact CategoryHomCarrier_empty_identity carrier
  · constructor
    · intro a b c f g fg left right comp
      exact CategoryHomCarrier_comp_closed left right comp
    · constructor
      · intro a b c d f g h fg gh left right first second third fgRel ghRel leftRel rightRel
        exact
          CategoryHomCarrier_comp_assoc_closed first second third fgRel ghRel leftRel rightRel
      · constructor
        · intro a b f left right homCarrier leftRel rightRel
          exact CategoryHomCarrier_identity_square_closed homCarrier leftRel rightRel
        · constructor
          · intro a a' b b' f f' sameSource sameTarget sameMorphism homCarrier
            exact
              CategoryHomCarrier_hsame_transport sameSource sameTarget sameMorphism homCarrier
          · intro a a' b b' f g sameSource sameTarget left right
            exact
              CategoryHomCarrier_endpoint_hsame_morphism_deterministic sameSource sameTarget
                left right

end BEDC.Derived.CategoryUp
