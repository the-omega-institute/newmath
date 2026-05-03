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

theorem AutomorphicAdeleGraph_visible_context_core_nonempty {p q domain value core : BHist} :
    AdeleHistoryCarrier domain -> AdeleHistoryCarrier value ->
      Cont (append p domain) (append value q) (append (append p core) q) ->
        hsame core BHist.Empty -> False := by
  intro domainCarrier valueCarrier visibleCont coreEmpty
  have prefixCont : Cont (append p domain) value (append p core) :=
    (cont_suffix_iff (a := append p domain) (b := append p core) (f := value) (p := q)).mp
      visibleCont
  have coreCont : Cont domain value core :=
    (cont_prefix_iff (p := p) (a := domain) (b := core) (f := value)).mp prefixCont
  exact AutomorphicAdeleGraph_cont_nonempty domainCarrier valueCarrier coreCont coreEmpty

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

theorem AutomorphicAdeleGraph_visible_context_result_nonempty {p q domain value graph : BHist} :
    AdeleHistoryCarrier domain -> AdeleHistoryCarrier value ->
      Cont (append p domain) (append value q) (append (append p graph) q) ->
        hsame (append (append p graph) q) BHist.Empty -> False := by
  intro domainCarrier valueCarrier visibleGraph resultEmpty
  have outerEmpty := append_eq_empty_iff.mp resultEmpty
  have innerEmpty := append_eq_empty_iff.mp outerEmpty.left
  exact AutomorphicAdeleGraph_visible_context_nonempty domainCarrier valueCarrier visibleGraph
    innerEmpty.right

end BEDC.Derived.AutomorphicUp
