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

end BEDC.Derived.ComplexSeriesUp
