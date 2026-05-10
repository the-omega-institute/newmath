import BEDC.Derived.DeRhamUp

namespace BEDC.Derived.DeRhamUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem DeRhamStandardBoundaryGraphLedger_endpoint_empty_from_rows
    {d : BHist -> BHist} {rows : List BHist} {endpoint : BHist} :
    DeRhamStandardBoundaryGraphLedger d rows endpoint ->
      (forall row : BHist, List.Mem row rows -> hsame row BHist.Empty) ->
        hsame endpoint BHist.Empty := by
  intro ledger rowEmpty
  induction ledger with
  | nil endpointEmpty =>
      exact endpointEmpty
  | cons packet _ thetaTailCont tailEndpointEmpty =>
      have thetaEmpty : hsame _ BHist.Empty :=
        rowEmpty _ (List.Mem.head _)
      have tailEmpty : hsame _ BHist.Empty :=
        tailEndpointEmpty (by
          intro row rowMem
          exact rowEmpty row (List.Mem.tail _ rowMem))
      have endpointEmpty : hsame _ BHist.Empty :=
        append_eq_empty_iff.mpr (And.intro thetaEmpty tailEmpty)
      exact hsame_trans thetaTailCont endpointEmpty

end BEDC.Derived.DeRhamUp
