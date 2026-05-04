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

theorem inBundle_bundleAppend_four_iff {PName : Type} {p : PName}
    {a b c d : ProbeBundle PName} :
    InBundle p (bundleAppend a (bundleAppend b (bundleAppend c d))) ↔
      InBundle p a ∨ InBundle p b ∨ InBundle p c ∨ InBundle p d := by
  constructor
  · intro inFour
    cases inBundle_bundleAppend_iff.mp inFour with
    | inl inA =>
        exact Or.inl inA
    | inr inBCD =>
        cases inBundle_bundleAppend_iff.mp inBCD with
        | inl inB =>
            exact Or.inr (Or.inl inB)
        | inr inCD =>
            cases inBundle_bundleAppend_iff.mp inCD with
            | inl inC =>
                exact Or.inr (Or.inr (Or.inl inC))
            | inr inD =>
                exact Or.inr (Or.inr (Or.inr inD))
  · intro inPart
    cases inPart with
    | inl inA =>
        exact inBundle_bundleAppend_iff.mpr (Or.inl inA)
    | inr inBCD =>
        cases inBCD with
        | inl inB =>
            exact inBundle_bundleAppend_iff.mpr
              (Or.inr (inBundle_bundleAppend_iff.mpr (Or.inl inB)))
        | inr inCD =>
            cases inCD with
            | inl inC =>
                exact inBundle_bundleAppend_iff.mpr
                  (Or.inr
                    (inBundle_bundleAppend_iff.mpr
                      (Or.inr (inBundle_bundleAppend_iff.mpr (Or.inl inC)))))
            | inr inD =>
                exact inBundle_bundleAppend_iff.mpr
                  (Or.inr
                    (inBundle_bundleAppend_iff.mpr
                      (Or.inr (inBundle_bundleAppend_iff.mpr (Or.inr inD)))))

theorem inBundle_member_split {PName : Type} {p : PName} :
    forall {bundle : ProbeBundle PName}, InBundle p bundle ->
      exists left : ProbeBundle PName, exists right : ProbeBundle PName,
        bundle = bundleAppend left (ProbeBundle.Bcons p right) := by
  intro bundle member
  induction bundle with
  | Bnil =>
      exact False.elim member
  | Bcons q tail ih =>
      cases member with
      | inl headSame =>
          cases headSame
          exact Exists.intro ProbeBundle.Bnil (Exists.intro tail rfl)
      | inr tailMember =>
          cases ih tailMember with
          | intro left splitRest =>
              cases splitRest with
              | intro right tailEq =>
                  cases tailEq
                  exact Exists.intro (ProbeBundle.Bcons q left) (Exists.intro right rfl)

theorem inBundle_member_split_iff {PName : Type} {p : PName}
    {bundle : ProbeBundle PName} :
    InBundle p bundle <->
      exists left : ProbeBundle PName, exists right : ProbeBundle PName,
        bundle = bundleAppend left (ProbeBundle.Bcons p right) := by
  constructor
  · intro member
    exact inBundle_member_split member
  · intro split
    cases split with
    | intro left splitRight =>
        cases splitRight with
        | intro right bundleEq =>
            cases bundleEq
            exact inBundle_bundleAppend_iff.mpr (Or.inr (Or.inl rfl))

end BEDC.FKernel.Bundle
