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

theorem SeriesPartialSum_pointwise_hsame_deterministic {zero zero' : BHist}
    {summand summand' : BHist -> BHist} (sameZero : hsame zero zero')
    (summandSame : forall {n : BHist}, UnaryHistory n -> hsame (summand n) (summand' n))
    {n left right : BHist} :
    UnaryHistory n -> SeriesPartialSum zero summand n left ->
      SeriesPartialSum zero' summand' n right -> hsame left right := by
  intro unaryN leftRow rightRow
  exact unary_history_induction
    (P := fun n => forall {left right : BHist}, SeriesPartialSum zero summand n left ->
      SeriesPartialSum zero' summand' n right -> hsame left right)
    (by
      intro left right leftRow rightRow
      cases leftRow
      cases rightRow
      exact sameZero)
    (by
      intro n unaryN ih left right leftRow rightRow
      cases leftRow with
      | step leftPrev leftCont =>
          cases rightRow with
          | step rightPrev rightCont =>
              exact cont_respects_hsame (ih leftPrev rightPrev) (summandSame unaryN)
                leftCont rightCont)
    n unaryN leftRow rightRow

theorem SeriesPartialSum_result_unary {zero : BHist} {summand : BHist -> BHist}
    (zeroUnary : UnaryHistory zero)
    (summandUnary : forall {n : BHist}, UnaryHistory n -> UnaryHistory (summand n))
    {n partialSum : BHist} :
    SeriesPartialSum zero summand n partialSum -> UnaryHistory n -> UnaryHistory partialSum := by
  intro row
  induction row with
  | zero =>
      intro _unaryN
      exact zeroUnary
  | step priorRow stepCont ih =>
      intro unaryStep
      have unaryN : UnaryHistory _ := unary_e1_inversion unaryStep
      have partialUnary : UnaryHistory _ := ih unaryN
      have summandNUnary : UnaryHistory _ := summandUnary unaryN
      exact unary_cont_closed partialUnary summandNUnary stepCont

theorem SeriesPartialSum_schema_bridge_endpoint_unary {zero : BHist}
    {summand modulus : BHist -> BHist} {n partialSum endpoint : BHist} :
    UnaryHistory zero ->
      (forall {k : BHist}, UnaryHistory k -> UnaryHistory (summand k)) ->
        (forall {k : BHist}, UnaryHistory k -> UnaryHistory (modulus k)) ->
          UnaryHistory n -> SeriesPartialSum zero summand n partialSum ->
            Cont partialSum (modulus n) endpoint ->
              UnaryHistory endpoint ∧ hsame endpoint (append partialSum (modulus n)) := by
  intro zeroUnary summandUnary modulusUnary unaryN partialSumRow endpointCont
  have partialSumUnary : UnaryHistory partialSum :=
    SeriesPartialSum_result_unary zeroUnary summandUnary partialSumRow unaryN
  have modulusNUnary : UnaryHistory (modulus n) := modulusUnary unaryN
  exact And.intro (unary_cont_closed partialSumUnary modulusNUnary endpointCont) endpointCont

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

theorem SeriesPartialSum_public_name_certificate {zero : BHist}
    {summand modulus : BHist -> BHist} {n partialSum endpoint : BHist} :
    UnaryHistory zero ->
      (forall {k : BHist}, UnaryHistory k -> UnaryHistory (summand k)) ->
        (forall {k : BHist}, UnaryHistory k -> UnaryHistory (modulus k)) ->
          UnaryHistory n ->
            SeriesPartialSum zero summand n partialSum ->
              Cont partialSum (modulus n) endpoint ->
                SemanticNameCert
                    (fun row : BHist =>
                      SeriesPartialSum zero summand n partialSum ∧ hsame row endpoint)
                    (fun row : BHist =>
                      SeriesPartialSum zero summand n partialSum ∧ hsame row endpoint)
                    (fun row : BHist =>
                      SeriesPartialSum zero summand n partialSum ∧ hsame row endpoint)
                    hsame ∧
                  UnaryHistory partialSum ∧ UnaryHistory endpoint ∧
                    hsame endpoint (append partialSum (modulus n)) := by
  intro zeroUnary summandUnary modulusUnary unaryN partialSumRow endpointCont
  have partialSumUnary : UnaryHistory partialSum :=
    SeriesPartialSum_result_unary zeroUnary summandUnary partialSumRow unaryN
  have endpointRows :=
    SeriesPartialSum_schema_bridge_endpoint_unary zeroUnary summandUnary modulusUnary unaryN
      partialSumRow endpointCont
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            SeriesPartialSum zero summand n partialSum ∧ hsame row endpoint)
          (fun row : BHist =>
            SeriesPartialSum zero summand n partialSum ∧ hsame row endpoint)
          (fun row : BHist =>
            SeriesPartialSum zero summand n partialSum ∧ hsame row endpoint)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint (And.intro partialSumRow (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert (And.intro partialSumUnary endpointRows)

end BEDC.Derived.SeriesUp
