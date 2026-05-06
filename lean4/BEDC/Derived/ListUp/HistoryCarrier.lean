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

inductive ListHistoryClassifier (S : BHist -> Prop) (Rel : BHist -> BHist -> Prop) :
    BHist -> BHist -> Prop where
  | nil {h k : BHist} :
      hsame h BHist.Empty -> hsame k BHist.Empty -> ListHistoryClassifier S Rel h k
  | cons {h k a b t u p q : BHist} :
      S a -> S b -> Rel a b -> ListHistoryClassifier S Rel t u -> Cont a t p ->
        Cont b u q -> hsame h (BHist.e1 p) -> hsame k (BHist.e1 q) ->
          ListHistoryClassifier S Rel h k

theorem ListHistoryClassifier_carrier_endpoints {S : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} {h k : BHist} :
    ListHistoryClassifier S Rel h k -> ListHistoryCarrier S h ∧ ListHistoryCarrier S k := by
  intro classifier
  induction classifier with
  | nil sameH sameK =>
      exact And.intro (ListHistoryCarrier.nil sameH) (ListHistoryCarrier.nil sameK)
  | cons sourceA sourceB _rel _tailClass contLeft contRight sameH sameK tailCarriers =>
      exact And.intro
        (ListHistoryCarrier.cons sourceA tailCarriers.left contLeft sameH)
        (ListHistoryCarrier.cons sourceB tailCarriers.right contRight sameK)

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
