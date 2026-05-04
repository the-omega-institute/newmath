import BEDC.Derived.ListUp.FramedEndpoint
import BEDC.Derived.ListUp.Reverse

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

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
