import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem CategoryHomCarrier_tail_comm_closed {a b c f g fg gf : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg -> Cont g f gf ->
      CategoryHomCarrier a c fg ∧ CategoryHomCarrier a c gf ∧ hsame fg gf := by
  intro left right fgRel gfRel
  have forwardCarrier : CategoryHomCarrier a c fg :=
    CategoryHomCarrier_comp_closed left right fgRel
  have sameTail : hsame fg gf :=
    CategoryHomCarrier_tail_comm_hsame left right fgRel gfRel
  have reverseCarrier : CategoryHomCarrier a c gf :=
    CategoryHomCarrier_hsame_transport (hsame_refl a) (hsame_refl c) sameTail forwardCarrier
  exact And.intro forwardCarrier (And.intro reverseCarrier sameTail)

theorem CategoryHomCarrier_tail_comm_public_readback {a b c f g fg gf : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg -> Cont g f gf ->
      CategoryHomCarrier a c fg ∧ CategoryHomCarrier a c gf ∧ hsame fg gf ∧
        (∀ {z : BHist}, CategoryHomCarrier a c z -> hsame fg z ∧ hsame gf z) := by
  intro left right fgRel gfRel
  have closed := CategoryHomCarrier_tail_comm_closed left right fgRel gfRel
  exact And.intro closed.left
    (And.intro closed.right.left
      (And.intro closed.right.right
        (by
          intro z displayed
          exact And.intro
            (CategoryHomCarrier_morphism_deterministic closed.left displayed)
            (CategoryHomCarrier_morphism_deterministic closed.right.left displayed))))

end BEDC.Derived.CategoryUp
