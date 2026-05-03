import BEDC.Derived.AdeleUp

namespace BEDC.Derived.AutomorphicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.AdeleUp

theorem AutomorphicAdeleGraph_cont_nonempty {domain value graph : BHist} :
    AdeleHistoryCarrier domain -> AdeleHistoryCarrier value -> Cont domain value graph ->
      hsame graph BHist.Empty -> False := by
  intro domainCarrier _valueCarrier graphCont graphEmpty
  have emptyGraph : Cont domain value BHist.Empty :=
    cont_result_hsame_transport graphCont graphEmpty
  have endpoints := cont_empty_result_inversion emptyGraph
  exact AdeleHistoryCarrier_not_empty domainCarrier endpoints.left

end BEDC.Derived.AutomorphicUp
