import BEDC.Derived.ListUp.FramedEndpoint

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem FramedListBridgeClassifier_nil_endpoint_inversion {A : BHist → Prop}
    {Rel : BHist → BHist → Prop} (cert : NameCert A Rel)
    (compat : ListSourceHsameCompatible A Rel) {h k : BHist} :
    hsame h (FramedListEndpoint []) →
      FramedListBridgeClassifier A Rel h k → hsame k (FramedListEndpoint []) := by
  intro sameH bridge
  have nilRepH : FramedListSpineRep A h ([] : ListCarrier BHist) := by
    constructor
    · intro x memX
      cases memX
    · exact sameH
  cases bridge with
  | intro xs bridgeTail =>
      cases bridgeTail with
      | intro ys bridgeData =>
          cases bridgeData with
          | intro repH bridgeRest =>
              cases bridgeRest with
              | intro repK _classified =>
                  have bridgeAgain : FramedListBridgeClassifier A Rel h k :=
                    Exists.intro xs
                      (Exists.intro ys
                        (And.intro repH (And.intro repK _classified)))
                  have classifiedNil :
                      ListClassifierSpec Rel ([] : ListCarrier BHist) ys :=
                    (FramedListBridgeClassifier_displayed_spine_exactness
                      cert compat nilRepH repK).mp bridgeAgain
                  cases ys with
                  | nil =>
                      exact repK.right
                  | cons _ _ =>
                      cases classifiedNil

end BEDC.Derived.ListUp
