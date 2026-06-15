import BEDC.Derived.GroundCompilerEventFlowAuditUp.NameCertObligations
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.GroundCompilerEventFlowAuditUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem GroundCompilerEventFlowAuditCarrier_lossless_gate
    {S F C L R G A H K P N sourceRead channelRead recognizerRead gateRead auditRead : BHist} :
    GroundCompilerEventFlowAuditCarrier S F C L R G A H K P N ->
      Cont S F sourceRead ->
        Cont C L channelRead ->
          Cont G A recognizerRead ->
            Cont channelRead recognizerRead gateRead ->
              Cont gateRead K auditRead ->
                UnaryHistory sourceRead ∧ UnaryHistory channelRead ∧
                  UnaryHistory recognizerRead ∧ UnaryHistory gateRead ∧
                    UnaryHistory auditRead ∧ Cont channelRead recognizerRead gateRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro carrier sourceRoute channelRoute recognizerRoute gateRoute auditRoute
  obtain ⟨sUnary, fUnary, cUnary, lUnary, _rUnary, gUnary, aUnary, _hUnary, kUnary,
    _pUnary, _nUnary⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed sUnary fUnary sourceRoute
  have channelUnary : UnaryHistory channelRead :=
    unary_cont_closed cUnary lUnary channelRoute
  have recognizerUnary : UnaryHistory recognizerRead :=
    unary_cont_closed gUnary aUnary recognizerRoute
  have gateUnary : UnaryHistory gateRead :=
    unary_cont_closed channelUnary recognizerUnary gateRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed gateUnary kUnary auditRoute
  exact
    ⟨sourceUnary, channelUnary, recognizerUnary, gateUnary, auditUnary, gateRoute⟩

end BEDC.Derived.GroundCompilerEventFlowAuditUp
