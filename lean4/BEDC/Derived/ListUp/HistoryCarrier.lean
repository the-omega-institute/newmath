import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

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

theorem ListHistoryCarrier_structural_recursion {A : BHist -> Prop} {P : BHist -> Prop}
    (nilP : forall {h : BHist}, hsame h BHist.Empty -> P h)
    (consP : forall {h a t p : BHist}, A a -> ListHistoryCarrier A t -> P t ->
      Cont a t p -> hsame h (BHist.e1 p) -> P h) :
    forall {h : BHist}, ListHistoryCarrier A h -> P h := by
  intro h carrier
  induction carrier with
  | nil empty =>
      exact nilP empty
  | cons source tail continuation endpoint tailP =>
      exact consP source tail tailP continuation endpoint

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

theorem ListHistoryClassifierRec_equivalence_fields {S : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} (cert : NameCert S Rel) :
    (forall {h : BHist}, ListHistoryCarrier S h -> ListHistoryClassifierRec S Rel h h) ∧
      (forall {h k : BHist}, ListHistoryClassifierRec S Rel h k ->
        ListHistoryClassifierRec S Rel k h) ∧
      (forall {h k : BHist}, ListHistoryClassifierRec S Rel h k ->
        ListHistoryCarrier S h ∧ ListHistoryCarrier S k) := by
  constructor
  · intro h carrier
    induction carrier with
    | nil empty =>
        exact ListHistoryClassifierRec.nil_nil empty empty
    | cons source tail continuation endpoint tailRefl =>
        exact ListHistoryClassifierRec.cons_cons source source
          (NameCert.equiv_refl cert source) tailRefl continuation continuation endpoint endpoint
  · constructor
    · intro h k classifier
      induction classifier with
      | nil_nil emptyH emptyK =>
          exact ListHistoryClassifierRec.nil_nil emptyK emptyH
      | cons_cons sourceA sourceB sameAB tailClassifier contA contB endH endK tailSymm =>
          exact ListHistoryClassifierRec.cons_cons sourceB sourceA
            (NameCert.equiv_symm cert sameAB) tailSymm contB contA endK endH
    · intro h k classifier
      exact ListHistoryClassifierRec_carrier_endpoints classifier

end BEDC.Derived.ListUp
