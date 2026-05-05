import BEDC.Derived.ComplexSeriesUp

namespace BEDC.Derived.ComplexSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.ComplexLimitUp

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

end BEDC.Derived.ComplexSeriesUp
