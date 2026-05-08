import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.SeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

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

end BEDC.Derived.SeriesUp
