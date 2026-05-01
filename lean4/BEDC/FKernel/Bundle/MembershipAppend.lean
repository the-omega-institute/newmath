import BEDC.FKernel.Bundle

namespace BEDC.FKernel.Bundle

theorem inBundle_bundleAppend_left_of_not_right {PName : Type} {p : PName}
    {left right : ProbeBundle PName} :
    InBundle p (bundleAppend left right) -> (InBundle p right -> False) -> InBundle p left := by
  induction left with
  | Bnil =>
      intro inAppend notRight
      exact False.elim (notRight inAppend)
  | Bcons q tail ih =>
      intro inAppend notRight
      cases inAppend with
      | inl head =>
          exact Or.inl head
      | inr tailOrRight =>
          exact Or.inr (ih tailOrRight notRight)

theorem inBundle_bundleAppend_right_of_not_left {PName : Type} {p : PName}
    {left right : ProbeBundle PName} :
    InBundle p (bundleAppend left right) -> (InBundle p left -> False) -> InBundle p right := by
  induction left with
  | Bnil =>
      intro inAppend _
      exact inAppend
  | Bcons q tail ih =>
      intro inAppend notLeft
      cases inAppend with
      | inl head =>
          exact False.elim (notLeft (Or.inl head))
      | inr tailOrRight =>
          exact ih tailOrRight (by
            intro tailMember
            exact notLeft (Or.inr tailMember))

theorem inBundle_bundleAppend_three_iff {PName : Type} {p : PName}
    {left middle right : ProbeBundle PName} :
    InBundle p (bundleAppend left (bundleAppend middle right)) ↔
      InBundle p left ∨ InBundle p middle ∨ InBundle p right := by
  constructor
  · intro inThree
    cases inBundle_bundleAppend_iff.mp inThree with
    | inl inLeft =>
        exact Or.inl inLeft
    | inr inMiddleRight =>
        cases inBundle_bundleAppend_iff.mp inMiddleRight with
        | inl inMiddle =>
            exact Or.inr (Or.inl inMiddle)
        | inr inRight =>
            exact Or.inr (Or.inr inRight)
  · intro inPart
    cases inPart with
    | inl inLeft =>
        exact inBundle_bundleAppend_iff.mpr (Or.inl inLeft)
    | inr inMiddleOrRight =>
        cases inMiddleOrRight with
        | inl inMiddle =>
            exact inBundle_bundleAppend_iff.mpr
              (Or.inr (inBundle_bundleAppend_iff.mpr (Or.inl inMiddle)))
        | inr inRight =>
            exact inBundle_bundleAppend_iff.mpr
              (Or.inr (inBundle_bundleAppend_iff.mpr (Or.inr inRight)))

end BEDC.FKernel.Bundle
