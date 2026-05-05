import BEDC.Derived.ComplexSeriesUp

namespace BEDC.Derived.ComplexSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexLimitUp

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

end BEDC.Derived.ComplexSeriesUp
