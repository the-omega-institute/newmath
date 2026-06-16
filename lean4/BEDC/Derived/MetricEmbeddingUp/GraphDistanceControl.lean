import BEDC.Derived.MetricEmbeddingUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.MetricEmbeddingUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

namespace GraphDistanceControl

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

end GraphDistanceControl

theorem MetricEmbeddingCarrier_graph_distance_control
    {X Y F D R S H C P N sourceRead graphRead controlRead sealedRead : BHist} :
    Cont X F sourceRead →
      Cont sourceRead Y graphRead →
        Cont graphRead D controlRead →
          Cont controlRead R sealedRead →
            UnaryHistory X →
              UnaryHistory Y →
                UnaryHistory F →
                  UnaryHistory D →
                    UnaryHistory R →
                      UnaryHistory sourceRead ∧ UnaryHistory graphRead ∧
                        UnaryHistory controlRead ∧ UnaryHistory sealedRead ∧
                          Cont X F sourceRead ∧ Cont sourceRead Y graphRead ∧
                            Cont graphRead D controlRead ∧
                              Cont controlRead R sealedRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro sourceRoute graphRoute controlRoute sealedRoute xUnary yUnary fUnary dUnary rUnary
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed xUnary fUnary sourceRoute
  have graphUnary : UnaryHistory graphRead :=
    unary_cont_closed sourceUnary yUnary graphRoute
  have controlUnary : UnaryHistory controlRead :=
    unary_cont_closed graphUnary dUnary controlRoute
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed controlUnary rUnary sealedRoute
  exact
    ⟨sourceUnary, graphUnary, controlUnary, sealedUnary, sourceRoute, graphRoute,
      controlRoute, sealedRoute⟩

end BEDC.Derived.MetricEmbeddingUp
