import BEDC.Derived.MetricEmbeddingUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricEmbeddingUp

open BEDC.Derived.MetricEmbeddingUp.TasteGate
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem MetricEmbeddingCarrier_graph_distance_control
    {X Y F D R S H C P N sourceGraph targetMetric comparisonSeal graphDistance : BHist} :
    metricEmbeddingFields (MetricEmbeddingUp.mk X Y F D R S H C P N) =
        [X, Y, F, D, R, S, H, C, P, N] →
      UnaryHistory X →
        UnaryHistory F →
          UnaryHistory Y →
            UnaryHistory D →
              UnaryHistory R →
                Cont X F sourceGraph →
                  Cont sourceGraph Y targetMetric →
                    Cont targetMetric D comparisonSeal →
                      Cont comparisonSeal R graphDistance →
                        UnaryHistory sourceGraph ∧ UnaryHistory targetMetric ∧
                          UnaryHistory comparisonSeal ∧ UnaryHistory graphDistance ∧
                            Cont X F sourceGraph ∧ Cont sourceGraph Y targetMetric ∧
                              Cont targetMetric D comparisonSeal ∧
                                Cont comparisonSeal R graphDistance := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro fieldRows xUnary fUnary yUnary dUnary rUnary sourceRoute targetRoute comparisonRoute
    graphRoute
  cases fieldRows
  have sourceUnary : UnaryHistory sourceGraph :=
    unary_cont_closed xUnary fUnary sourceRoute
  have targetUnary : UnaryHistory targetMetric :=
    unary_cont_closed sourceUnary yUnary targetRoute
  have comparisonUnary : UnaryHistory comparisonSeal :=
    unary_cont_closed targetUnary dUnary comparisonRoute
  have graphUnary : UnaryHistory graphDistance :=
    unary_cont_closed comparisonUnary rUnary graphRoute
  exact
    ⟨sourceUnary, targetUnary, comparisonUnary, graphUnary, sourceRoute, targetRoute,
      comparisonRoute, graphRoute⟩

end BEDC.Derived.MetricEmbeddingUp
