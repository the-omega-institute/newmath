import BEDC.FKernel.Cont

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

inductive ListHistoryCarrier (S : BHist -> Prop) : BHist -> Prop where
  | nil {h : BHist} :
      hsame h BHist.Empty -> ListHistoryCarrier S h
  | cons {h a t p : BHist} :
      S a -> ListHistoryCarrier S t -> Cont a t p -> hsame h (BHist.e1 p) ->
        ListHistoryCarrier S h

theorem ListHistoryCarrier_generated_cases {S : BHist -> Prop} {h : BHist} :
    ListHistoryCarrier S h ->
      hsame h BHist.Empty ∨
        exists a : BHist, exists t : BHist, exists p : BHist,
          S a ∧ ListHistoryCarrier S t ∧ Cont a t p ∧ hsame h (BHist.e1 p) := by
  intro carrier
  cases carrier with
  | nil empty =>
      exact Or.inl empty
  | cons source tail continuation endpoint =>
      exact Or.inr
        (Exists.intro _
          (Exists.intro _
            (Exists.intro _
              (And.intro source (And.intro tail (And.intro continuation endpoint))))))

end BEDC.Derived.ListUp
