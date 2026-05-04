import BEDC.Derived.ListUp.FramedEndpoint
import BEDC.Derived.ListUp.Reverse

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem FramedListPublicReverse_functional_involutive {A : BHist → Prop}
    {Rel : BHist → BHist → Prop} (cert : NameCert A Rel)
    (compat : ListSourceHsameCompatible A Rel) :
      (let Rev := fun h k : BHist =>
        ∃ xs : ListCarrier BHist,
          FramedListSpineRep A h xs ∧ FramedListSpineRep A k xs.reverse;
        (∀ {h k : BHist}, Rev h k → FramedListHistoryCarrier A h ∧
        FramedListHistoryCarrier A k) ∧
        (∀ {h k : BHist}, Rev h k → Rev k h) ∧
          (∀ {h k k' : BHist}, Rev h k → Rev h k' →
              FramedListBridgeClassifier A Rel k k') ∧
              (∀ {h h' k k' : BHist}, FramedListBridgeClassifier A Rel h h' →
                Rev h k → Rev h' k' → FramedListBridgeClassifier A Rel k k')) := by
    have appendAssocPure :
        ∀ xs ys zs : List BHist, (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
      intro xs
      induction xs with
      | nil =>
          intro ys zs
          rfl
      | cons x xs ih =>
          intro ys zs
          exact congrArg (List.cons x) (ih ys zs)
    have appendNilPure : ∀ xs : List BHist, xs ++ [] = xs := by
      intro xs
      induction xs with
      | nil =>
          rfl
      | cons x xs ih =>
          exact congrArg (List.cons x) ih
    have reverseAuxPure :
        ∀ xs ys : List BHist, List.reverseAux xs ys = List.reverseAux xs [] ++ ys := by
      intro xs
      induction xs with
      | nil =>
          intro ys
          rfl
      | cons x xs ih =>
          intro ys
          exact (ih (x :: ys)).trans
            ((appendAssocPure (List.reverseAux xs []) [x] ys).symm.trans
              (congrArg (fun tail => tail ++ ys) (ih [x]).symm))
    have reverseConsPure :
        ∀ x : BHist, ∀ xs : List BHist, List.reverse (x :: xs) = List.reverse xs ++ [x] := by
      intro x xs
      change List.reverseAux xs [x] = List.reverseAux xs [] ++ [x]
      exact reverseAuxPure xs [x]
    have reverseAppendPure :
        ∀ xs ys : List BHist, (xs ++ ys).reverse = ys.reverse ++ xs.reverse := by
      intro xs
      induction xs with
      | nil =>
          intro ys
          change List.reverse ys = List.reverse ys ++ []
          exact (appendNilPure (List.reverse ys)).symm
      | cons x xs ih =>
          intro ys
          exact (reverseConsPure x (xs ++ ys)).trans
            ((congrArg (fun tail => tail ++ [x]) (ih ys)).trans
              ((appendAssocPure (List.reverse ys) (List.reverse xs) [x]).trans
                (congrArg (fun tail => List.reverse ys ++ tail) (reverseConsPure x xs).symm)))
    have reverseReversePure : ∀ xs : List BHist, xs.reverse.reverse = xs := by
      intro xs
      induction xs with
      | nil =>
          rfl
      | cons x xs ih =>
          exact (congrArg List.reverse (reverseConsPure x xs)).trans
            ((reverseAppendPure xs.reverse [x]).trans
              ((congrArg (fun tail => [x].reverse ++ tail) ih).trans rfl))
    constructor
    · intro h k reverseData
      cases reverseData with
      | intro xs reps =>
          exact And.intro (Exists.intro xs reps.left) (Exists.intro xs.reverse reps.right)
    · constructor
      · intro h k reverseData
        cases reverseData with
        | intro xs reps =>
            have repHReverse :
                FramedListSpineRep A h xs.reverse.reverse := by
              exact Eq.mpr
                (congrArg (fun zs => FramedListSpineRep A h zs) (reverseReversePure xs))
                reps.left
            exact Exists.intro xs.reverse (And.intro reps.right repHReverse)
      · constructor
        · intro h k k' reverseLeft reverseRight
          cases reverseLeft with
          | intro xs leftReps =>
              cases reverseRight with
              | intro ys rightReps =>
                  have classifiedXY : ListClassifierSpec Rel xs ys :=
                    FramedListSpineRep_coherence compat leftReps.left rightReps.left
                  have classifiedReverse : ListClassifierSpec Rel xs.reverse ys.reverse :=
                    (ListClassifierSpec_reverse_iff (sameA := Rel) (xs := xs) (ys := ys)).mp
                      classifiedXY
                  exact (FramedListBridgeClassifier_displayed_spine_exactness cert compat
                    leftReps.right rightReps.right).mpr classifiedReverse
        · intro h h' k k' bridge reverseLeft reverseRight
          cases reverseLeft with
          | intro xs leftReps =>
              cases reverseRight with
              | intro ys rightReps =>
                  have classifiedXY : ListClassifierSpec Rel xs ys :=
                    (FramedListBridgeClassifier_displayed_spine_exactness cert compat
                      leftReps.left rightReps.left).mp bridge
                  have classifiedReverse : ListClassifierSpec Rel xs.reverse ys.reverse :=
                    (ListClassifierSpec_reverse_iff (sameA := Rel) (xs := xs) (ys := ys)).mp
                      classifiedXY
                  exact (FramedListBridgeClassifier_displayed_spine_exactness cert compat
                    leftReps.right rightReps.right).mpr classifiedReverse

theorem FramedListPublicReverse_classifier_functional {A : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} (cert : NameCert A Rel)
    (compat : ListSourceHsameCompatible A Rel) {h k k' : BHist} :
    (∃ xs : ListCarrier BHist,
      FramedListSpineRep A h xs ∧ FramedListSpineRep A k xs.reverse) ->
      (∃ ys : ListCarrier BHist,
        FramedListSpineRep A h ys ∧ FramedListSpineRep A k' ys.reverse) ->
        FramedListBridgeClassifier A Rel k k' := by
  intro leftReverse rightReverse
  cases leftReverse with
  | intro xs leftData =>
      cases rightReverse with
      | intro ys rightData =>
          have classifiedSpines : ListClassifierSpec Rel xs ys :=
            FramedListSpineRep_coherence compat leftData.left rightData.left
          have classifiedReverses : ListClassifierSpec Rel xs.reverse ys.reverse :=
            (ListClassifierSpec_reverse_iff (sameA := Rel)).mp classifiedSpines
          exact (FramedListBridgeClassifier_displayed_spine_exactness cert compat
            leftData.right rightData.right).mpr classifiedReverses

end BEDC.Derived.ListUp
