import BEDC.Derived.MetricEmbeddingUp.TasteGate
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.MetricEmbeddingUp.GraphDistanceControl

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem MetricEmbeddingGraphDistance_control
    {X F Y R sourceGraph targetGraph comparisonRead : BHist}
    (unaryX : UnaryHistory X)
    (unaryF : UnaryHistory F)
    (unaryY : UnaryHistory Y)
    (unaryR : UnaryHistory R)
    (sourceRoute : Cont X F sourceGraph)
    (targetRoute : Cont sourceGraph Y targetGraph)
    (comparisonRoute : Cont targetGraph R comparisonRead) :
    UnaryHistory sourceGraph ∧ UnaryHistory targetGraph ∧ UnaryHistory comparisonRead ∧
      Cont X F sourceGraph ∧ Cont sourceGraph Y targetGraph ∧
        Cont targetGraph R comparisonRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  have unarySourceGraph : UnaryHistory sourceGraph :=
    unary_cont_closed unaryX unaryF sourceRoute
  have unaryTargetGraph : UnaryHistory targetGraph :=
    unary_cont_closed unarySourceGraph unaryY targetRoute
  have unaryComparisonRead : UnaryHistory comparisonRead :=
    unary_cont_closed unaryTargetGraph unaryR comparisonRoute
  exact
    ⟨unarySourceGraph, unaryTargetGraph, unaryComparisonRead,
      sourceRoute, targetRoute, comparisonRoute⟩

end BEDC.Derived.MetricEmbeddingUp.GraphDistanceControl
