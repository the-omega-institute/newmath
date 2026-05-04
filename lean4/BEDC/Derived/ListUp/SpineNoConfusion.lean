import BEDC.Derived.ListUp.FramedEndpoint
import BEDC.Derived.ListUp.BridgeTransport

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist

theorem FramedListSpineRep_nil_cons_no_confusion {A : BHist → Prop} {h a : BHist}
    {xs : ListCarrier BHist} :
    FramedListSpineRep A h [] → FramedListSpineRep A h (List.cons a xs) → False := by
  intro nilRep consRep
  have sameEndpoints :
      hsame (FramedListEndpoint []) (FramedListEndpoint (List.cons a xs)) :=
    hsame_trans (hsame_symm nilRep.right) consRep.right
  exact
    (FramedListEndpoint_no_confusion_cons_inversion
      (a := a) (b := a) (xs := xs) (ys := xs)).left sameEndpoints

end BEDC.Derived.ListUp
