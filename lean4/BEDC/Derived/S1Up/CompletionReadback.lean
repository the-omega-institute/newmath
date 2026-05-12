import BEDC.Derived.S1Up

namespace BEDC.Derived.S1Up

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

def SOneDisplayedCompletionReadback
    (alpha : BHist -> BHist) (a x y e p c : BHist) : Prop :=
  SOneHistoryCarrier x y e p ∧ hsame (alpha a) p ∧ hsame c p

theorem SOneDisplayedCompletionReadback_source_separation
    {alpha : BHist -> BHist}
    (alpha_injective : forall {u v : BHist}, hsame (alpha u) (alpha v) -> hsame u v)
    {a a' x y e p c x' y' e' p' c' : BHist} :
    SOneDisplayedCompletionReadback alpha a x y e p c ->
      SOneDisplayedCompletionReadback alpha a' x' y' e' p' c' ->
        (Cont x y p ∧ Cont x' y' p' ∧ (hsame c c' -> hsame a a')) ∧
          ((hsame a a' -> False) -> (hsame c c' -> False)) := by
  intro left right
  obtain ⟨leftCarrier, sameAlphaLeft, sameEndpointLeft⟩ := left
  obtain ⟨rightCarrier, sameAlphaRight, sameEndpointRight⟩ := right
  have sourceSame : hsame c c' -> hsame a a' := by
    intro sameEndpoint
    apply alpha_injective
    exact
      hsame_trans sameAlphaLeft
        (hsame_trans (hsame_symm sameEndpointLeft)
          (hsame_trans sameEndpoint
            (hsame_trans sameEndpointRight (hsame_symm sameAlphaRight))))
  exact
    ⟨⟨leftCarrier.right.right.right, rightCarrier.right.right.right, sourceSame⟩,
      fun sourceSeparated sameEndpoint => sourceSeparated (sourceSame sameEndpoint)⟩

end BEDC.Derived.S1Up
