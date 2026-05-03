import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CategoryHomCarrier_stability_law_package :
    (∀ {a : BHist}, UnaryHistory a -> CategoryHomCarrier a a BHist.Empty) ∧
      (∀ {a b c f g fg : BHist},
        CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
          CategoryHomCarrier a c fg) ∧
      (∀ {a b c d f g h fg gh left right : BHist},
        CategoryHomCarrier a b f -> CategoryHomCarrier b c g ->
          CategoryHomCarrier c d h -> Cont f g fg -> Cont g h gh -> Cont fg h left ->
            Cont f gh right ->
              CategoryHomCarrier a d left ∧ CategoryHomCarrier a d right ∧ hsame left right) ∧
      (∀ {a b f left right : BHist},
        CategoryHomCarrier a b f -> Cont BHist.Empty f left -> Cont f BHist.Empty right ->
          CategoryHomCarrier a b left ∧ CategoryHomCarrier a b right ∧ hsame left right) := by
  constructor
  · intro a carrier
    exact CategoryHomCarrier_empty_identity carrier
  · constructor
    · intro a b c f g fg left right comp
      exact CategoryHomCarrier_comp_closed left right comp
    · constructor
      · intro a b c d f g h fg gh left right first second third fgRel ghRel leftRel rightRel
        exact CategoryHomCarrier_comp_assoc_closed first second third fgRel ghRel leftRel rightRel
      · intro a b f left right homCarrier leftRel rightRel
        exact CategoryHomCarrier_identity_square_closed homCarrier leftRel rightRel

end BEDC.Derived.CategoryUp
