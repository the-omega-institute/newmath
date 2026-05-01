import BEDC.Derived.ListUp

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist

def PairFrame : BHist → BHist → BHist
  | BHist.Empty, tail => BHist.e0 tail
  | BHist.e0 head, tail => BHist.e1 (BHist.e0 (PairFrame head tail))
  | BHist.e1 head, tail => BHist.e1 (BHist.e1 (PairFrame head tail))

def FramedListEndpoint : ListCarrier BHist → BHist
  | [] => BHist.e0 BHist.Empty
  | head :: tail => BHist.e1 (PairFrame head (FramedListEndpoint tail))

theorem PairFrame_hsame_injective {u u' t t' : BHist} :
    hsame (PairFrame u t) (PairFrame u' t') → hsame u u' ∧ hsame t t' := by
  intro same
  induction u generalizing u' t t' with
  | Empty =>
      cases u' with
      | Empty =>
          change hsame (BHist.e0 t) (BHist.e0 t') at same
          constructor
          · rfl
          · exact hsame_e0_iff.mp same
      | e0 u' =>
          change hsame (BHist.e0 t) (BHist.e1 (BHist.e0 (PairFrame u' t'))) at same
          exact False.elim (not_hsame_e0_e1 same)
      | e1 u' =>
          change hsame (BHist.e0 t) (BHist.e1 (BHist.e1 (PairFrame u' t'))) at same
          exact False.elim (not_hsame_e0_e1 same)
  | e0 u ih =>
      cases u' with
      | Empty =>
          change hsame (BHist.e1 (BHist.e0 (PairFrame u t))) (BHist.e0 t') at same
          exact False.elim (not_hsame_e1_e0 same)
      | e0 u' =>
          change hsame (BHist.e1 (BHist.e0 (PairFrame u t)))
            (BHist.e1 (BHist.e0 (PairFrame u' t'))) at same
          have inner : hsame (BHist.e0 (PairFrame u t)) (BHist.e0 (PairFrame u' t')) :=
            hsame_e1_iff.mp same
          have recursive :
              hsame u u' ∧ hsame t t' :=
            ih (u' := u') (t := t) (t' := t') (hsame_e0_iff.mp inner)
          constructor
          · exact hsame_e0_congr recursive.left
          · exact recursive.right
      | e1 u' =>
          change hsame (BHist.e1 (BHist.e0 (PairFrame u t)))
            (BHist.e1 (BHist.e1 (PairFrame u' t'))) at same
          have inner : hsame (BHist.e0 (PairFrame u t)) (BHist.e1 (PairFrame u' t')) :=
            hsame_e1_iff.mp same
          exact False.elim (not_hsame_e0_e1 inner)
  | e1 u ih =>
      cases u' with
      | Empty =>
          change hsame (BHist.e1 (BHist.e1 (PairFrame u t))) (BHist.e0 t') at same
          exact False.elim (not_hsame_e1_e0 same)
      | e0 u' =>
          change hsame (BHist.e1 (BHist.e1 (PairFrame u t)))
            (BHist.e1 (BHist.e0 (PairFrame u' t'))) at same
          have inner : hsame (BHist.e1 (PairFrame u t)) (BHist.e0 (PairFrame u' t')) :=
            hsame_e1_iff.mp same
          exact False.elim (not_hsame_e1_e0 inner)
      | e1 u' =>
          change hsame (BHist.e1 (BHist.e1 (PairFrame u t)))
            (BHist.e1 (BHist.e1 (PairFrame u' t'))) at same
          have inner : hsame (BHist.e1 (PairFrame u t)) (BHist.e1 (PairFrame u' t')) :=
            hsame_e1_iff.mp same
          have recursive :
              hsame u u' ∧ hsame t t' :=
            ih (u' := u') (t := t) (t' := t') (hsame_e1_iff.mp inner)
          constructor
          · exact hsame_e1_congr recursive.left
          · exact recursive.right

theorem FramedListEndpoint_no_confusion_cons_inversion {a b : BHist}
    {xs ys : ListCarrier BHist} :
    (hsame (FramedListEndpoint []) (FramedListEndpoint (a :: xs)) → False) ∧
      (hsame (FramedListEndpoint (a :: xs)) (FramedListEndpoint []) → False) ∧
        (hsame (FramedListEndpoint (a :: xs)) (FramedListEndpoint (b :: ys)) →
          hsame a b ∧ hsame (FramedListEndpoint xs) (FramedListEndpoint ys)) := by
  constructor
  · intro same
    change hsame (BHist.e0 BHist.Empty)
      (BHist.e1 (PairFrame a (FramedListEndpoint xs))) at same
    exact not_hsame_e0_e1 same
  · constructor
    · intro same
      change hsame (BHist.e1 (PairFrame a (FramedListEndpoint xs)))
        (BHist.e0 BHist.Empty) at same
      exact not_hsame_e1_e0 same
    · intro same
      change hsame (BHist.e1 (PairFrame a (FramedListEndpoint xs)))
        (BHist.e1 (PairFrame b (FramedListEndpoint ys))) at same
      exact PairFrame_hsame_injective (hsame_e1_iff.mp same)

end BEDC.Derived.ListUp
