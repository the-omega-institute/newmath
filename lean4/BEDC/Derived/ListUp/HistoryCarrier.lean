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

inductive ListHistoryClassifierRec (S : BHist -> Prop) (sameS : BHist -> BHist -> Prop) :
    BHist -> BHist -> Prop where
  | nil_nil {h k : BHist} :
      hsame h BHist.Empty -> hsame k BHist.Empty -> ListHistoryClassifierRec S sameS h k
  | cons_cons {h k a b t u p q : BHist} :
      S a -> S b -> sameS a b -> ListHistoryClassifierRec S sameS t u ->
        Cont a t p -> Cont b u q -> hsame h (BHist.e1 p) -> hsame k (BHist.e1 q) ->
          ListHistoryClassifierRec S sameS h k

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

theorem ListHistoryClassifierRec_carrier_endpoints {S : BHist -> Prop}
    {sameS : BHist -> BHist -> Prop} {h k : BHist} :
    ListHistoryClassifierRec S sameS h k -> ListHistoryCarrier S h ∧ ListHistoryCarrier S k := by
  intro classifier
  induction classifier with
  | nil_nil emptyH emptyK =>
      exact And.intro (ListHistoryCarrier.nil emptyH) (ListHistoryCarrier.nil emptyK)
  | cons_cons sourceA sourceB _sameAB _tailClassifier contA contB endH endK tailEndpoints =>
      exact And.intro
        (ListHistoryCarrier.cons sourceA tailEndpoints.left contA endH)
        (ListHistoryCarrier.cons sourceB tailEndpoints.right contB endK)

end BEDC.Derived.ListUp
