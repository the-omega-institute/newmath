import BEDC.Derived.ListUp.SpineBridge

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem ListSpineBridgeClassifier_represented_spine_constructor_exactness
    {A : BHist -> Prop} {Rel : BHist -> BHist -> Prop} (cert : NameCert A Rel)
    (coherent : forall {h : BHist} {xs ys : ListCarrier BHist},
      ListSpineRep A h xs -> ListSpineRep A h ys -> ListClassifierSpec Rel xs ys)
    {h k a b : BHist} {xs ys : ListCarrier BHist} :
    (ListSpineRep A h [] -> ListSpineRep A k (b :: ys) ->
      ListSpineBridgeClassifier A Rel h k -> False) ∧
      (ListSpineRep A h (a :: xs) -> ListSpineRep A k [] ->
        ListSpineBridgeClassifier A Rel h k -> False) ∧
        (ListSpineRep A h (a :: xs) -> ListSpineRep A k (b :: ys) ->
          (ListSpineBridgeClassifier A Rel h k ↔
            Rel a b ∧ ListClassifierSpec Rel xs ys)) := by
  constructor
  · intro repNil repCons bridge
    have classified :
        ListClassifierSpec Rel ([] : ListCarrier BHist) (b :: ys) :=
      (ListSpineBridgeClassifier_displayed_spine_exactness cert coherent repNil repCons).mp
        bridge
    cases classified
  · constructor
    · intro repCons repNil bridge
      have classified :
          ListClassifierSpec Rel (a :: xs) ([] : ListCarrier BHist) :=
        (ListSpineBridgeClassifier_displayed_spine_exactness cert coherent repCons repNil).mp
          bridge
      cases classified
    · intro repConsA repConsB
      constructor
      · intro bridge
        have classified :
            ListClassifierSpec Rel (a :: xs) (b :: ys) :=
          (ListSpineBridgeClassifier_displayed_spine_exactness cert coherent repConsA
            repConsB).mp bridge
        exact (ListClassifierSpec_case_exactness (sameA := Rel)).right.left.mp classified
      · intro classified
        have consClassified : ListClassifierSpec Rel (a :: xs) (b :: ys) :=
          (ListClassifierSpec_case_exactness (sameA := Rel)).right.left.mpr classified
        exact (ListSpineBridgeClassifier_displayed_spine_exactness cert coherent repConsA
          repConsB).mpr consClassified

end BEDC.Derived.ListUp
