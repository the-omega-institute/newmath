import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricEmbeddingUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

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
