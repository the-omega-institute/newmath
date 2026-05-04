import BEDC.Derived.ListUp.FramedEndpoint

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist

theorem FramedListSpineRep_cons_endpoint_injective {A : BHist -> Prop}
    {h k a b : BHist} {xs ys : ListCarrier BHist} :
    FramedListSpineRep A h (List.cons a xs) ->
      FramedListSpineRep A k (List.cons b ys) ->
        hsame h k ->
          hsame (BHist.e1 (PairFrame a (FramedListEndpoint xs)))
            (BHist.e1 (PairFrame b (FramedListEndpoint ys))) ∧
            hsame a b ∧ hsame (FramedListEndpoint xs) (FramedListEndpoint ys) := by
  intro repH repK sameHK
  cases repH with
  | intro _entriesH endpointH =>
      cases repK with
      | intro _entriesK endpointK =>
          have sameEndpoints :
              hsame (FramedListEndpoint (a :: xs)) (FramedListEndpoint (b :: ys)) :=
            hsame_trans (hsame_symm endpointH) (hsame_trans sameHK endpointK)
          have framedSame :
              hsame (BHist.e1 (PairFrame a (FramedListEndpoint xs)))
                (BHist.e1 (PairFrame b (FramedListEndpoint ys))) :=
            sameEndpoints
          have split :
              hsame a b ∧ hsame (FramedListEndpoint xs) (FramedListEndpoint ys) :=
            (FramedListEndpoint_no_confusion_cons_inversion
              (a := a) (b := b) (xs := xs) (ys := ys)).right.right sameEndpoints
          exact And.intro framedSame split

end BEDC.Derived.ListUp
