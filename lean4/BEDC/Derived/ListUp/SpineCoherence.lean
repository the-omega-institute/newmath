import BEDC.Derived.ListUp.SpineRep

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

def ListConsBoundaryCoherent (A : BHist -> Prop)
    (Rel : BHist -> BHist -> BHist -> Prop) : Prop :=
  forall {m a a' t t' p p' : BHist} {xs xs' : ListCarrier BHist},
    A a -> A a' -> ListSpineRep A t xs -> ListSpineRep A t' xs' ->
      Cont a t p -> Cont a' t' p' -> hsame m (BHist.e1 p) ->
        hsame m (BHist.e1 p') -> Rel m a a' ∧ ListClassifierSpec (Rel m) xs xs'

protected theorem ListSpineRep_coherent_from_cons_boundary {A : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop}
    (boundary :
      forall {m a a' t t' p p' : BHist} {xs xs' : ListCarrier BHist},
        A a -> A a' -> ListSpineRep A t xs -> ListSpineRep A t' xs' ->
          Cont a t p -> Cont a' t' p' -> hsame m (BHist.e1 p) ->
            hsame m (BHist.e1 p') -> Rel a a' ∧ ListClassifierSpec Rel xs xs') :
    forall {h : BHist} {xs ys : ListCarrier BHist},
      ListSpineRep A h xs -> ListSpineRep A h ys -> ListClassifierSpec Rel xs ys := by
  intro h xs ys repX repY
  cases repX with
  | nil endpointX =>
      cases repY with
      | nil endpointY =>
          constructor
      | cons sourceY tailY contY endpointY =>
          exact False.elim
            (ListSpineRep_nil_cons_no_confusion
              (h := h) (ListSpineRep.nil endpointX) sourceY tailY contY endpointY)
  | cons sourceX tailX contX endpointX =>
      cases repY with
      | nil endpointY =>
          exact False.elim
            (ListSpineRep_nil_cons_no_confusion
              (h := h) (ListSpineRep.nil endpointY) sourceX tailX contX endpointX)
      | cons sourceY tailY contY endpointY =>
          exact boundary sourceX sourceY tailX tailY contX contY endpointX endpointY

end BEDC.Derived.ListUp
