import BEDC.Derived.BanachUp
import BEDC.Derived.OperatorIdealUp

namespace BEDC.Derived.NuclearUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.BanachUp
open BEDC.Derived.OperatorIdealUp

theorem NuclearCarrier_obligation
    {banachSource banachTarget compactRow rankLedger endpoint : BHist} :
    BanachSingletonCarrier banachSource -> BanachSingletonCarrier banachTarget ->
      OperatorIdealTraceClassCarrier compactRow -> UnaryHistory rankLedger ->
        Cont (append banachSource banachTarget) compactRow endpoint ->
          UnaryHistory endpoint ∧ UnaryHistory compactRow ∧ UnaryHistory rankLedger := by
  intro sourceCarrier targetCarrier compactCarrier rankUnary endpointCont
  have sourceUnary : UnaryHistory banachSource :=
    unary_transport unary_empty (hsame_symm sourceCarrier.left)
  have targetUnary : UnaryHistory banachTarget :=
    unary_transport unary_empty (hsame_symm targetCarrier.left)
  have sourceTargetUnary : UnaryHistory (append banachSource banachTarget) :=
    unary_cont_closed sourceUnary targetUnary (cont_intro rfl)
  have compactUnary : UnaryHistory compactRow :=
    (OperatorIdealTraceClass_downstream_boundary_readback compactCarrier).left
  exact And.intro
    (unary_cont_closed sourceTargetUnary compactUnary endpointCont)
    (And.intro compactUnary rankUnary)

end BEDC.Derived.NuclearUp
