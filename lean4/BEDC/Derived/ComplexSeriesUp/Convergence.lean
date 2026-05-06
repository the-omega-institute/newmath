import BEDC.Derived.ComplexSeriesUp

namespace BEDC.Derived.ComplexSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp
open BEDC.Derived.ComplexLimitUp
open BEDC.Derived.RatUp

def ComplexSeriesClassifierSpec (zero : BHist) (c : BHist -> BHist) (S T : BHist) : Prop :=
  ComplexSeriesConv zero c S ∧ hsame S T

theorem ComplexSeriesConv_limit_transport_successor_step {zero : BHist} {c : BHist -> BHist}
    {S T n P Q : BHist} (sameLimit : hsame S T) (conv : ComplexSeriesConv zero c S)
    (partialSum : ComplexPartSum zero c n P) (stepCont : Cont P (c n) Q) :
    ComplexSeriesConv zero c T ∧ ComplexPartSum zero c (BHist.e1 n) Q := by
  constructor
  · cases conv with
    | intro ps convRest =>
        cases convRest with
        | intro N convRest =>
            cases convRest with
            | intro M data =>
                exact Exists.intro ps
                  (Exists.intro N
                    (Exists.intro M
                      (And.intro data.left
                        (ComplexLimit_hsame_transport sameLimit data.right))))
  · exact ComplexPartSum.step partialSum stepCont

theorem ComplexSeriesClassifierSpec_limit_transport {zero : BHist} {c : BHist -> BHist}
    {S T U : BHist} :
    ComplexSeriesClassifierSpec zero c S T -> hsame T U ->
      exists ps : BHist -> BHist, exists N : BHist -> BHist, exists M : BHist -> BHist,
        (forall n : BHist, UnaryHistory n -> ComplexPartSum zero c n (ps n)) ∧
          ComplexLimit ps N U M ∧ ComplexSeriesClassifierSpec zero c S U := by
  intro classified sameTU
  cases classified with
  | intro conv sameST =>
      cases conv with
      | intro ps convRest =>
          cases convRest with
          | intro N convRest =>
              cases convRest with
              | intro M data =>
                  have sameSU : hsame S U := hsame_trans sameST sameTU
                  exact Exists.intro ps
                    (Exists.intro N
                      (Exists.intro M
                        (And.intro data.left
                          (And.intro (ComplexLimit_hsame_transport sameSU data.right)
                            (And.intro
                              (Exists.intro ps
                                (Exists.intro N
                                  (Exists.intro M (And.intro data.left data.right))))
                              sameSU)))))

theorem ComplexSeriesConv_pointwise_source_limit_transport {zero zero' S T : BHist}
    {c d ps' : BHist -> BHist} :
    hsame zero zero' ->
      (forall {n : BHist}, UnaryHistory n -> hsame (c n) (d n)) ->
        hsame S T -> ComplexSeriesConv zero c S ->
          (forall n : BHist, UnaryHistory n -> ComplexPartSum zero' d n (ps' n)) ->
            ComplexSeriesConv zero' d T := by
  intro sameZero pointwise sameLimit conv targetPartials
  cases conv with
  | intro ps convRest =>
      cases convRest with
      | intro N convRest =>
          cases convRest with
          | intro M data =>
              have samePartials :
                  forall {n : BHist}, UnaryHistory n -> hsame (ps n) (ps' n) := by
                intro n unaryN
                exact ComplexPartSum_pointwise_hsame_deterministic sameZero pointwise unaryN
                  (data.left n unaryN) (targetPartials n unaryN)
              have targetLimitS : ComplexLimit ps' N S M :=
                ComplexLimit_sequence_hsame_transport samePartials data.right
              exact Exists.intro ps'
                (Exists.intro N
                  (Exists.intro M
                    (And.intro targetPartials
                      (ComplexLimit_hsame_transport sameLimit targetLimitS))))

theorem ComplexPartSum_index_unary {zero : BHist} {c : BHist -> BHist} {n S : BHist} :
    ComplexPartSum zero c n S -> UnaryHistory n := by
  intro sum
  induction sum with
  | zero =>
      exact BEDC.FKernel.Unary.unary_empty
  | step _previous _stepContinuation ih =>
      exact BEDC.FKernel.Unary.unary_e1_closed ih

theorem ComplexPartSum_pointwise_append_partials {a b : BHist -> BHist} {n SA SB : BHist}
    (aUnary : forall {m : BHist}, UnaryHistory m -> UnaryHistory (a m))
    (bUnary : forall {m : BHist}, UnaryHistory m -> UnaryHistory (b m)) :
    ComplexPartSum BHist.Empty a n SA -> ComplexPartSum BHist.Empty b n SB ->
      ComplexPartSum BHist.Empty (fun m : BHist => append (a m) (b m)) n (append SA SB) := by
  intro left
  induction left generalizing SB with
  | zero =>
      intro right
      cases right with
      | zero =>
          exact ComplexPartSum.zero
  | step leftPrevious leftStep ih =>
      intro right
      cases right with
      | step rightPrevious rightStep =>
          have previousUnaryA :
              UnaryHistory _ :=
            ComplexPartSum_result_unary unary_empty aUnary leftPrevious
          have previousUnaryB :
              UnaryHistory _ :=
            ComplexPartSum_result_unary unary_empty bUnary rightPrevious
          have termUnaryA :
              UnaryHistory (a _) :=
            aUnary (ComplexPartSum_index_unary leftPrevious)
          have combinedPrevious := ih rightPrevious
          refine ComplexPartSum.step combinedPrevious ?_
          apply cont_intro
          exact
            ((congrArg (fun source : BHist => append source _) leftStep).trans
              ((congrArg (append _) rightStep).trans
                ((append_assoc _ (a _) _).trans
                  ((congrArg (append _) (append_assoc _ _ _).symm).trans
                    ((congrArg (fun source : BHist => append _ (append source _))
                        (unary_append_comm termUnaryA previousUnaryB)).trans
                        ((congrArg (append _) (append_assoc _ _ _)).trans
                          (append_assoc _ _ _).symm))))))

theorem ComplexPartSum_pointwise_append_partials_unique {a b : BHist -> BHist}
    {n SA SB T : BHist}
    (aUnary : forall {m : BHist}, UnaryHistory m -> UnaryHistory (a m))
    (bUnary : forall {m : BHist}, UnaryHistory m -> UnaryHistory (b m)) :
    ComplexPartSum BHist.Empty a n SA -> ComplexPartSum BHist.Empty b n SB ->
      ComplexPartSum BHist.Empty (fun m : BHist => append (a m) (b m)) n T ->
        hsame T (append SA SB) := by
  intro left right target
  have canonical :=
    ComplexPartSum_pointwise_append_partials aUnary bUnary left right
  exact hsame_symm (ComplexPartSum_deterministic canonical target)

theorem ComplexTermSeqCarrier_pointwise_append_components {c d : BHist -> BHist} :
    ComplexTermSeqCarrier c -> ComplexTermSeqCarrier d ->
      ComplexTermSeqCarrier (fun n : BHist => append (c n) (d n)) ∧
        forall n : BHist, UnaryHistory n ->
          exists real imag : BHist,
            RatHistoryCarrier real ∧ RatHistoryCarrier imag ∧
              Cont real imag (append (c n) (d n)) := by
  intro cCarrier dCarrier
  constructor
  · intro n unaryN
    exact ComplexHistoryCarrier_append_unary_closed (cCarrier n unaryN)
      (ComplexHistoryCarrier_unary (dCarrier n unaryN))
  · intro n unaryN
    cases ComplexHistoryCarrier_append_unary_closed (cCarrier n unaryN)
        (ComplexHistoryCarrier_unary (dCarrier n unaryN)) with
    | intro real rest =>
        cases rest with
        | intro imag data =>
            exact Exists.intro real (Exists.intro imag data)

end BEDC.Derived.ComplexSeriesUp
