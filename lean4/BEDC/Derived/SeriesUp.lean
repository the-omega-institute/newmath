import BEDC.Derived.SeqUp
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.SeriesUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.SeqUp

theorem SeriesPartialSumLedger_step_transport {PointCarrier : BHist -> Prop}
    {PointClassifier : BHist -> BHist -> Prop}
    (cert : NameCert PointCarrier PointClassifier)
    (addClosed : forall {a b out : BHist},
      PointCarrier a -> PointCarrier b -> Cont a b out -> PointCarrier out)
    {summand summand' partialSum : BHist -> BHist} {n step step' : BHist} :
    SeqRootSource PointCarrier partialSum ->
      SeqPointwiseClassifier PointCarrier PointClassifier summand summand' ->
        UnaryHistory n -> Cont (partialSum n) (summand n) step ->
          Cont (partialSum n) (summand' n) step' -> hsame step step' ->
            PointCarrier step ∧ PointCarrier step' ∧
              PointClassifier (summand n) (summand' n) ∧
                PointClassifier (summand' n) (summand n) := by
  intro partialSource pointwise unaryN stepCont stepCont' _sameStep
  have partialCarrier : PointCarrier (partialSum n) := partialSource unaryN
  have row := pointwise unaryN
  have stepCarrier : PointCarrier step :=
    addClosed partialCarrier row.left stepCont
  have stepCarrier' : PointCarrier step' :=
    addClosed partialCarrier row.right.left stepCont'
  exact And.intro stepCarrier
    (And.intro stepCarrier'
      (And.intro row.right.right (NameCert.equiv_symm cert row.right.right)))

theorem SeriesModulusStability_transport {PointCarrier : BHist -> Prop}
    {PointClassifier : BHist -> BHist -> Prop}
    (cert : NameCert PointCarrier PointClassifier)
    {partialSum partialSum' : BHist -> BHist} :
    SeqPointwiseClassifier PointCarrier PointClassifier partialSum partialSum' ->
      (forall {k n m : BHist}, UnaryHistory k -> UnaryHistory n -> UnaryHistory m ->
        PointClassifier (partialSum n) (partialSum m)) ->
        forall {k n m : BHist}, UnaryHistory k -> UnaryHistory n -> UnaryHistory m ->
          PointClassifier (partialSum' n) (partialSum' m) := by
  intro pointwise modulus k n m unaryK unaryN unaryM
  have rowN := pointwise unaryN
  have rowM := pointwise unaryM
  have sameN : PointClassifier (partialSum' n) (partialSum n) :=
    NameCert.equiv_symm cert rowN.right.right
  have sameNM : PointClassifier (partialSum' n) (partialSum m) :=
    NameCert.equiv_trans cert sameN (modulus unaryK unaryN unaryM)
  exact NameCert.equiv_trans cert sameNM rowM.right.right

end BEDC.Derived.SeriesUp
