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

theorem ListSpineRep_cons_endpoint_shape {A : BHist -> Prop} {h a : BHist}
    {xs : ListCarrier BHist} :
    ListSpineRep A h (a :: xs) ->
      ∃ t p : BHist, A a ∧ ListSpineRep A t xs ∧ Cont a t p ∧
        hsame h (BHist.e1 p) := by
  intro rep
  cases rep with
  | cons head tail ledger endpoint =>
      exact Exists.intro _ (Exists.intro _ (And.intro head
        (And.intro tail (And.intro ledger endpoint))))

theorem ListSpineRep_append_representation {A : BHist -> Prop} {h k : BHist}
    {xs ys : ListCarrier BHist} :
    ListSpineRep A h xs -> ListSpineRep A k ys ->
      exists r : BHist, ListSpineRep A r (xs ++ ys) := by
  intro left right
  induction left with
  | nil _endpoint =>
      exact Exists.intro k right
  | cons head _tail _spine _endpoint tailAppend =>
      cases tailAppend with
      | intro r rep =>
          exact Exists.intro _
            (ListSpineRep.cons head rep (cont_intro rfl)
              (hsame_refl _))

end BEDC.Derived.ListUp
