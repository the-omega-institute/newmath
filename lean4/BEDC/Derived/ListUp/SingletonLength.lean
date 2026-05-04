import BEDC.Derived.ListUp.PublicLength
import BEDC.Derived.ListUp.SingletonSource

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist

theorem FramedListBridgeClassifier_singleton_zero_public_length_iff_empty {a0 h k : BHist} :
    (FramedListBridgeClassifier (ListSingletonHistorySource a0) hsame h k ∧
      FramedListPublicLength (ListSingletonHistorySource a0) h 0 ∧
        FramedListPublicLength (ListSingletonHistorySource a0) k 0) ↔
      hsame h (BHist.e0 BHist.Empty) ∧ hsame k (BHist.e0 BHist.Empty) := by
  constructor
  · intro data
    exact And.intro
      ((FramedListPublicLength_constructor_endpoint_readback
        (A := ListSingletonHistorySource a0) (h := h) (n := 0)).left.mp data.right.left)
      ((FramedListPublicLength_constructor_endpoint_readback
        (A := ListSingletonHistorySource a0) (h := k) (n := 0)).left.mp data.right.right)
  · intro endpoints
    have repH :
        FramedListSpineRep (ListSingletonHistorySource a0) h ([] : ListCarrier BHist) :=
      And.intro
        (fun x mem => by
          cases mem)
        endpoints.left
    have repK :
        FramedListSpineRep (ListSingletonHistorySource a0) k ([] : ListCarrier BHist) :=
      And.intro
        (fun x mem => by
          cases mem)
        endpoints.right
    have classified :
        ListClassifierSpec hsame ([] : ListCarrier BHist) ([] : ListCarrier BHist) :=
      (ListClassifierSpec_case_exactness (sameA := hsame)).left
    have bridge :
        FramedListBridgeClassifier (ListSingletonHistorySource a0) hsame h k :=
      Exists.intro ([] : ListCarrier BHist)
        (Exists.intro ([] : ListCarrier BHist)
          (And.intro repH (And.intro repK classified)))
    exact And.intro bridge
      (And.intro
        ((FramedListPublicLength_constructor_endpoint_readback
          (A := ListSingletonHistorySource a0) (h := h) (n := 0)).left.mpr endpoints.left)
        ((FramedListPublicLength_constructor_endpoint_readback
          (A := ListSingletonHistorySource a0) (h := k) (n := 0)).left.mpr endpoints.right))

end BEDC.Derived.ListUp
