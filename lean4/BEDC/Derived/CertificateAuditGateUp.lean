import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.CertificateAuditGateUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CertificateAuditGateBridgeBoundary
    {I S R D A H C P N publicRead bridgeRead : BHist} :
    UnaryHistory I ->
      UnaryHistory S ->
        UnaryHistory R ->
          Cont I S publicRead ->
            Cont publicRead R bridgeRead ->
              UnaryHistory publicRead ∧ UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro inputUnary surfaceUnary readUnary publicRoute bridgeRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed inputUnary surfaceUnary publicRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed publicUnary readUnary bridgeRoute
  exact ⟨publicUnary, bridgeUnary⟩

end BEDC.Derived.CertificateAuditGateUp
