import BEDC.Derived.IntUp

namespace BEDC.Derived.IntUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem IntPairCarrier_magnitude_pair_induction {P : BHist -> BHist -> Prop} :
    P BHist.Empty BHist.Empty ->
      (forall p n : BHist, UnaryHistory p -> UnaryHistory n -> P p n ->
        P (BHist.e1 p) n) ->
      (forall p n : BHist, UnaryHistory p -> UnaryHistory n -> P p n ->
        P p (BHist.e1 n)) ->
      forall {p n : BHist}, IntPairCarrier p n -> P p n := by
  intro base leftStep rightStep p n carrier
  cases carrier with
  | intro unaryP unaryN =>
      have emptyLeft : forall n : BHist, UnaryHistory n -> P BHist.Empty n := by
        intro n unaryN
        exact unary_history_induction
          base
          (fun n unaryN ih => rightStep BHist.Empty n unary_empty unaryN ih)
          n
          unaryN
      exact unary_history_induction
        (P := fun p => forall n : BHist, UnaryHistory n -> P p n)
        emptyLeft
        (fun p unaryP ih => by
          intro n unaryN
          exact leftStep p n unaryP unaryN (ih n unaryN))
        p
        unaryP
        n
        unaryN

end BEDC.Derived.IntUp
