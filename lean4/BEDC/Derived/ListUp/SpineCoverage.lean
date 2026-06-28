import BEDC.Derived.ListUp.HistoryCarrier
import BEDC.Derived.ListUp.SpineRep

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem ListSpineRepresentation_coverage {A : BHist -> Prop} {h : BHist} :
    (ListHistoryCarrier A h ↔ exists xs : ListCarrier BHist, ListSpineRep A h xs) ∧
      (forall {a t p : BHist} {xs : ListCarrier BHist},
        A a -> ListSpineRep A t xs -> Cont a t p ->
          ListSpineRep A (BHist.e1 p) (a :: xs)) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  constructor
  · constructor
    · intro carrier
      induction carrier with
      | nil endpoint =>
          exact Exists.intro [] (ListSpineRep.nil endpoint)
      | cons source _tail continuation endpoint tailSpine =>
          cases tailSpine with
          | intro xs rep =>
              exact Exists.intro (_ :: xs)
                (ListSpineRep.cons source rep continuation endpoint)
    · intro covered
      cases covered with
      | intro xs rep =>
          induction rep with
          | nil endpoint =>
              exact ListHistoryCarrier.nil endpoint
          | cons source _tail continuation endpoint tailCarrier =>
              exact ListHistoryCarrier.cons source tailCarrier continuation endpoint
  · intro a t p xs source rep continuation
    exact ListSpineRep.cons source rep continuation (hsame_refl (BHist.e1 p))

end BEDC.Derived.ListUp
