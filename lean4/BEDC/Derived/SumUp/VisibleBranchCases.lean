import BEDC.Derived.SumUp

namespace BEDC.Derived.SumUp

open BEDC.FKernel.Hist

theorem SumHistoryCarrier_visible_branch_cases {Left Right : BHist -> Prop} {h : BHist} :
    SumHistoryCarrier Left Right h ->
      (exists l : BHist, Left l ∧ hsame h (BHist.e0 l)) ∨
        (exists r : BHist, Right r ∧ hsame h (BHist.e1 r)) := by
  intro carrier
  cases carrier with
  | inl leftData =>
      cases leftData with
      | intro l data =>
          exact Or.inl (Exists.intro l (And.intro data.right data.left))
  | inr rightData =>
      cases rightData with
      | intro r data =>
          exact Or.inr (Exists.intro r (And.intro data.right data.left))

end BEDC.Derived.SumUp
