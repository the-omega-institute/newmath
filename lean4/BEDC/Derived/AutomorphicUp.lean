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

theorem AutomorphicAdeleGraph_visible_context_value_readback
    {p q domain value value' graph : BHist} :
    AdeleHistoryCarrier domain -> AdeleHistoryCarrier value ->
      Cont (append p domain) (append value q) (append (append p graph) q) ->
        Cont domain value' graph -> hsame value value' ∧ (hsame graph BHist.Empty -> False) := by
  intro domainCarrier valueCarrier visibleGraph displayedGraph
  have rightPeeled : Cont (append p domain) value (append p graph) :=
    (cont_suffix_iff (a := append p domain) (b := append p graph) (f := value)
      (p := q)).mp visibleGraph
  have baseGraph : Cont domain value graph :=
    (cont_prefix_iff (p := p) (a := domain) (b := graph) (f := value)).mp rightPeeled
  exact And.intro (cont_left_cancel baseGraph displayedGraph)
    (AutomorphicAdeleGraph_cont_nonempty domainCarrier valueCarrier baseGraph)

theorem AutomorphicAdeleGraph_visible_context_domain_readback
    {p q domain domain' value graph : BHist} :
    AdeleHistoryCarrier domain -> AdeleHistoryCarrier value ->
      Cont (append p domain) (append value q) (append (append p graph) q) ->
        Cont domain' value graph -> hsame domain domain' ∧
          (hsame graph BHist.Empty -> False) := by
  intro domainCarrier valueCarrier visibleGraph displayedGraph
  have rightPeeled : Cont (append p domain) value (append p graph) :=
    (cont_suffix_iff (a := append p domain) (b := append p graph) (f := value)
      (p := q)).mp visibleGraph
  have baseGraph : Cont domain value graph :=
    (cont_prefix_iff (p := p) (a := domain) (b := graph) (f := value)).mp rightPeeled
  exact And.intro (cont_right_cancel baseGraph displayedGraph)
    (AutomorphicAdeleGraph_cont_nonempty domainCarrier valueCarrier baseGraph)

theorem AutomorphicAdeleGraph_visible_context_core_deterministic_nonempty
    {p q domain value core core' : BHist} :
    AdeleHistoryCarrier domain -> AdeleHistoryCarrier value ->
      Cont (append p domain) (append value q) (append (append p core) q) ->
      Cont (append p domain) (append value q) (append (append p core') q) ->
        hsame core core' ∧ (hsame core BHist.Empty -> False) ∧
          (hsame core' BHist.Empty -> False) := by
  intro domainCarrier valueCarrier visibleCore visibleCore'
  have rightPeeled : Cont (append p domain) value (append p core) :=
    (cont_suffix_iff (a := append p domain) (b := append p core) (f := value)
      (p := q)).mp visibleCore
  have rightPeeled' : Cont (append p domain) value (append p core') :=
    (cont_suffix_iff (a := append p domain) (b := append p core') (f := value)
      (p := q)).mp visibleCore'
  have coreCont : Cont domain value core :=
    (cont_prefix_iff (p := p) (a := domain) (b := core) (f := value)).mp rightPeeled
  have coreCont' : Cont domain value core' :=
    (cont_prefix_iff (p := p) (a := domain) (b := core') (f := value)).mp rightPeeled'
  exact And.intro (cont_deterministic coreCont coreCont')
    (And.intro (AutomorphicAdeleGraph_cont_nonempty domainCarrier valueCarrier coreCont)
      (AutomorphicAdeleGraph_cont_nonempty domainCarrier valueCarrier coreCont'))

theorem AutomorphicAdeleGraph_visible_context_result_nonempty {p q domain value graph : BHist} :
    AdeleHistoryCarrier domain -> AdeleHistoryCarrier value ->
      Cont (append p domain) (append value q) (append (append p graph) q) ->
        hsame (append (append p graph) q) BHist.Empty -> False := by
  intro domainCarrier valueCarrier visibleGraph resultEmpty
  have outerEmpty := append_eq_empty_iff.mp resultEmpty
  have innerEmpty := append_eq_empty_iff.mp outerEmpty.left
  exact AutomorphicAdeleGraph_visible_context_nonempty domainCarrier valueCarrier visibleGraph
    innerEmpty.right

theorem AutomorphicAdeleGraph_visible_result_nonempty {p q domain value result : BHist} :
    AdeleHistoryCarrier domain -> AdeleHistoryCarrier value ->
      Cont (append p domain) (append value q) result -> hsame result BHist.Empty -> False := by
  intro domainCarrier _valueCarrier visibleCont resultEmpty
  have emptyCont : Cont (append p domain) (append value q) BHist.Empty :=
    cont_result_hsame_transport visibleCont resultEmpty
  have endpoints := cont_empty_result_inversion emptyCont
  have domainEmpty : hsame domain BHist.Empty :=
    (append_eq_empty_iff.mp endpoints.left).right
  exact AdeleHistoryCarrier_not_empty domainCarrier domainEmpty

theorem AutomorphicAdeleGraph_visible_context_result_hsame_transport
    {p q domain value graph graph' : BHist} :
    AdeleHistoryCarrier domain -> AdeleHistoryCarrier value ->
      Cont (append p domain) (append value q) (append (append p graph) q) ->
        hsame graph graph' ->
          Cont (append p domain) (append value q) (append (append p graph') q) ∧
            (hsame graph' BHist.Empty -> False) := by
  intro domainCarrier valueCarrier visibleGraph sameGraph
  have sameResult : hsame (append (append p graph) q) (append (append p graph') q) :=
    congrArg (fun h => append (append p h) q) sameGraph
  have visibleGraph' :
      Cont (append p domain) (append value q) (append (append p graph') q) :=
    cont_result_hsame_transport visibleGraph sameResult
  exact And.intro visibleGraph'
    (AutomorphicAdeleGraph_visible_context_nonempty domainCarrier valueCarrier visibleGraph')

theorem AutomorphicAdeleGraph_visible_context_value_hsame_transport
    {p q domain value value' graph : BHist} :
    AdeleHistoryCarrier domain -> AdeleHistoryCarrier value' ->
      Cont (append p domain) (append value q) (append (append p graph) q) ->
        hsame value value' ->
          Cont (append p domain) (append value' q) (append (append p graph) q) ∧
            (hsame graph BHist.Empty -> False) := by
  intro domainCarrier valueCarrier' visibleGraph sameValue
  have sameVisibleValue : hsame (append value q) (append value' q) :=
    congrArg (fun h => append h q) sameValue
  have visibleGraph' :
      Cont (append p domain) (append value' q) (append (append p graph) q) :=
    cont_hsame_transport (hsame_refl (append p domain)) sameVisibleValue
      (hsame_refl (append (append p graph) q)) visibleGraph
  exact And.intro visibleGraph'
    (AutomorphicAdeleGraph_visible_context_nonempty domainCarrier valueCarrier' visibleGraph')

theorem AutomorphicAdeleGraph_visible_context_core_readback {p q domain value graph core : BHist} :
    AdeleHistoryCarrier domain -> AdeleHistoryCarrier value ->
      Cont (append p domain) (append value q) (append (append p graph) q) ->
        hsame (append (append p graph) q) (append (append p core) q) ->
          hsame graph core ∧ (hsame core BHist.Empty -> False) := by
  intro domainCarrier valueCarrier visibleGraph sameVisible
  have sameNested : hsame (append p (append graph q)) (append p (append core q)) :=
    hsame_trans (hsame_symm (append_assoc p graph q))
      (hsame_trans sameVisible (append_assoc p core q))
  have sameCore : hsame graph core :=
    (append_hsame_common_context_cancel_iff (hsame_refl p) (hsame_refl q)).mp sameNested
  have visibleCore : Cont (append p domain) (append value q) (append (append p core) q) :=
    cont_result_hsame_transport visibleGraph sameVisible
  exact And.intro sameCore
    (AutomorphicAdeleGraph_visible_context_core_nonempty domainCarrier valueCarrier visibleCore)

end BEDC.Derived.AutomorphicUp
