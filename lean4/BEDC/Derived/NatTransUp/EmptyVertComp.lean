import BEDC.Derived.NatTransUp

namespace BEDC.Derived.NatTransUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

theorem NatTransPrefixComponentCarrier_vert_comp_empty_iff {p q r a eta theta : BHist} :
    NatTransPrefixComponentCarrier p q a eta ->
      NatTransPrefixComponentCarrier q r a theta ->
        (Cont eta theta BHist.Empty <->
          hsame eta BHist.Empty ∧ hsame theta BHist.Empty ∧ hsame p q ∧ hsame q r) := by
  intro left right
  constructor
  · intro comp
    have base := (CategoryHomCarrier_empty_composite_iff left.right.right.right
      right.right.right.right).mp comp
    exact ⟨base.left, base.right.left,
      append_right_cancel (k := a) base.right.right.left,
      append_right_cancel (k := a) base.right.right.right⟩
  · intro data
    have sourceSame : hsame (append p a) (append q a) := by
      cases data.right.right.left
      exact hsame_refl (append p a)
    have targetSame : hsame (append q a) (append r a) := by
      cases data.right.right.right
      exact hsame_refl (append q a)
    exact (CategoryHomCarrier_empty_composite_iff left.right.right.right
      right.right.right.right).mpr
      ⟨data.left, data.right.left, sourceSame, targetSame⟩

theorem NatTransPrefixComponentCarrier_vert_comp_result_empty_iff
    {p q r a eta theta composite : BHist} :
    NatTransPrefixComponentCarrier p q a eta ->
      NatTransPrefixComponentCarrier q r a theta ->
        Cont eta theta composite ->
          (hsame composite BHist.Empty ↔
            hsame eta BHist.Empty ∧ hsame theta BHist.Empty ∧ hsame p q ∧ hsame q r) := by
  intro left right comp
  have componentResult :=
    CategoryHomCarrier_comp_result_empty_iff
      left.right.right.right right.right.right.right comp
  constructor
  · intro compositeEmpty
    have homData := Iff.mp componentResult compositeEmpty
    exact
      And.intro homData.left
        (And.intro homData.right.left
          (And.intro
            (append_right_cancel (k := a) homData.right.right.left)
            (append_right_cancel (k := a) homData.right.right.right)))
  · intro data
    have sourceSame : hsame (append p a) (append q a) := by
      cases data.right.right.left
      exact hsame_refl (append p a)
    have targetSame : hsame (append q a) (append r a) := by
      cases data.right.right.right
      exact hsame_refl (append q a)
    exact Iff.mpr componentResult
      (And.intro data.left (And.intro data.right.left (And.intro sourceSame targetSame)))

end BEDC.Derived.NatTransUp
