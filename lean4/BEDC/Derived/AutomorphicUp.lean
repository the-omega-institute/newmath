import BEDC.FKernel.Cont.Cancellation
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

theorem AutomorphicAdeleGraph_visible_context_nonempty {p q domain value graph : BHist} :
    AdeleHistoryCarrier domain -> AdeleHistoryCarrier value ->
      Cont (append p domain) (append value q) (append (append p graph) q) ->
        hsame graph BHist.Empty -> False := by
  intro domainCarrier valueCarrier visibleGraph graphEmpty
  have rightPeeled : Cont (append p domain) value (append p graph) :=
    (cont_suffix_iff (a := append p domain) (b := append p graph) (f := value)
      (p := q)).mp visibleGraph
  have baseGraph : Cont domain value graph :=
    (cont_prefix_iff (p := p) (a := domain) (b := graph) (f := value)).mp rightPeeled
  exact AutomorphicAdeleGraph_cont_nonempty domainCarrier valueCarrier baseGraph graphEmpty

end BEDC.Derived.AutomorphicUp
