import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary.History
import BEDC.Derived.MetricTopologyUp.TasteGate

namespace BEDC.Derived.MetricTopologyUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem MetricTopologyCarrier_ball_basis_scope
    {M B T R Q H C P N ballOpen topologyOpen publicOpen : BHist} :
    UnaryHistory M ->
      UnaryHistory B ->
        UnaryHistory T ->
          UnaryHistory R ->
            UnaryHistory Q ->
              Cont M B ballOpen ->
                Cont ballOpen T topologyOpen ->
                  Cont topologyOpen R publicOpen ->
                    hsame publicOpen N ->
                      UnaryHistory ballOpen ∧ UnaryHistory topologyOpen ∧
                        UnaryHistory publicOpen ∧ Cont M B ballOpen ∧
                          Cont ballOpen T topologyOpen ∧ Cont topologyOpen R publicOpen ∧
                            hsame publicOpen N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro mUnary bUnary tUnary rUnary _qUnary ballCont topologyCont publicCont publicSame
  have ballUnary : UnaryHistory ballOpen :=
    unary_cont_closed mUnary bUnary ballCont
  have topologyUnary : UnaryHistory topologyOpen :=
    unary_cont_closed ballUnary tUnary topologyCont
  have publicUnary : UnaryHistory publicOpen :=
    unary_cont_closed topologyUnary rUnary publicCont
  exact
    ⟨ballUnary, topologyUnary, publicUnary, ballCont, topologyCont, publicCont, publicSame⟩

end BEDC.Derived.MetricTopologyUp
