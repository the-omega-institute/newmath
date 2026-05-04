import BEDC.Derived.ListUp.FramedEndpoint

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist

theorem FramedListBridgeClassifier_e1_endpoint_hsame_transport {A : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} {h k h' k' : BHist} :
    FramedListBridgeClassifier A Rel (BHist.e1 h) (BHist.e1 k) ->
      hsame h h' -> hsame k k' ->
        FramedListBridgeClassifier A Rel (BHist.e1 h') (BHist.e1 k') := by
  intro bridge sameH sameK
  cases bridge with
  | intro xs bridgeRest =>
      cases bridgeRest with
      | intro ys bridgeData =>
          cases bridgeData with
          | intro leftRep rest =>
              cases rest with
              | intro rightRep classified =>
                  exact Exists.intro xs
                    (Exists.intro ys
                      (And.intro
                        (FramedListSpineRep_hsame_transport leftRep
                          (hsame_e1_congr sameH))
                        (And.intro
                          (FramedListSpineRep_hsame_transport rightRep
                            (hsame_e1_congr sameK))
                          classified)))

end BEDC.Derived.ListUp
