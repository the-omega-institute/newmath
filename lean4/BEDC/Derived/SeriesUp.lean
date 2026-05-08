import BEDC.Derived.SeqUp
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.SeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.SeqUp

inductive SeriesPartialSum (zero : BHist) (summand : BHist -> BHist) :
    BHist -> BHist -> Prop where
  | zero : SeriesPartialSum zero summand BHist.Empty zero
  | step {n partialSum next : BHist} :
      SeriesPartialSum zero summand n partialSum ->
        Cont partialSum (summand n) next ->
          SeriesPartialSum zero summand (BHist.e1 n) next

theorem SeriesPartialSum_transport {zero : BHist} {summand : BHist -> BHist}
    {n partialSum next transported : BHist} :
    UnaryHistory n -> SeriesPartialSum zero summand n partialSum ->
      Cont partialSum (summand n) next -> hsame next transported ->
        SeriesPartialSum zero summand (BHist.e1 n) transported ∧
          Cont partialSum (summand n) transported := by
  intro _unaryN sumRow nextCont sameNext
  have transportedCont : Cont partialSum (summand n) transported :=
    cont_result_hsame_transport nextCont sameNext
  exact And.intro (SeriesPartialSum.step sumRow transportedCont) transportedCont

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

theorem SeriesSourceCarrierBoundary_obligation {PointCarrier : BHist -> Prop}
    {PointClassifier : BHist -> BHist -> Prop} (cert : NameCert PointCarrier PointClassifier)
    {summand partialSum modulus : BHist -> BHist} :
    SeqRootSource PointCarrier summand -> SeqRootSource PointCarrier partialSum ->
      (forall {n : BHist}, UnaryHistory n -> UnaryHistory (modulus n)) ->
        forall {n : BHist}, UnaryHistory n ->
          PointCarrier (summand n) ∧ PointCarrier (partialSum n) ∧
            UnaryHistory (modulus n) ∧ PointClassifier (summand n) (summand n) := by
  intro summandSource partialSource modulusUnary n unaryN
  have summandCarrier : PointCarrier (summand n) := summandSource unaryN
  have partialCarrier : PointCarrier (partialSum n) := partialSource unaryN
  have modulusCarrier : UnaryHistory (modulus n) := modulusUnary unaryN
  exact And.intro summandCarrier
    (And.intro partialCarrier
      (And.intro modulusCarrier (NameCert.equiv_refl cert summandCarrier)))

end BEDC.Derived.SeriesUp
