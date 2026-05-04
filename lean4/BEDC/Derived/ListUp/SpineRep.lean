import BEDC.Derived.ListUp
import BEDC.FKernel.Cont

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

inductive ListSpineRep (A : BHist -> Prop) : BHist -> ListCarrier BHist -> Prop
  | nil {h : BHist} : hsame h BHist.Empty -> ListSpineRep A h []
  | cons {h a t p : BHist} {xs : ListCarrier BHist} :
      A a -> ListSpineRep A t xs -> Cont a t p -> hsame h (BHist.e1 p) ->
        ListSpineRep A h (a :: xs)

theorem ListSpineRep_nil_cons_no_confusion {A : BHist -> Prop} {h a t p : BHist}
    {xs : List BHist} :
    ListSpineRep A h [] -> A a -> ListSpineRep A t xs -> Cont a t p ->
      hsame h (BHist.e1 p) -> False := by
  intro nilRep _head _tail _cont endpoint
  cases nilRep with
  | nil nilEndpoint =>
      exact not_hsame_emp_e1 (hsame_trans (hsame_symm nilEndpoint) endpoint)

theorem ListSpineRep_cons_hsame_transport {A : BHist -> Prop} {h h' a t p : BHist}
    {xs : ListCarrier BHist} :
    A a -> ListSpineRep A t xs -> Cont a t p -> hsame h (BHist.e1 p) ->
      hsame h h' -> ListSpineRep A h' (a :: xs) := by
  intro head tail spine endpoint sameEndpoint
  exact ListSpineRep.cons head tail spine (hsame_trans (hsame_symm sameEndpoint) endpoint)

end BEDC.Derived.ListUp
