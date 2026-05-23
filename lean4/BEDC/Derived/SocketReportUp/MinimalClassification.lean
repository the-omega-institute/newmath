import BEDC.Derived.SocketReportUp.TasteGate
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SocketReportUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SocketReportUp_minimal_classification [AskSetup] [PackageSetup]
    {x : SocketReportUp} {siteRead kindRead : BHist} :
    (∃ site requestedSupply socketKind auditGate transport continuation provenance localName :
      BHist,
      x = SocketReportUp.mk site requestedSupply socketKind auditGate transport continuation
        provenance localName ∧
        UnaryHistory site ∧ UnaryHistory requestedSupply ∧ UnaryHistory socketKind ∧
          UnaryHistory auditGate ∧ Cont site requestedSupply siteRead ∧
            Cont socketKind auditGate kindRead) →
      ∃ site requestedSupply socketKind auditGate transport continuation provenance localName :
        BHist,
        x = SocketReportUp.mk site requestedSupply socketKind auditGate transport continuation
          provenance localName ∧
          List.Mem requestedSupply (socketReportFields x) ∧
            List.Mem socketKind (socketReportFields x) ∧
              List.Mem auditGate (socketReportFields x) ∧
                UnaryHistory siteRead ∧ UnaryHistory kindRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro accepted
  obtain ⟨site, requestedSupply, socketKind, auditGate, transport, continuation,
    provenance, localName, packetEq, siteUnary, requestedSupplyUnary, socketKindUnary,
    auditGateUnary, siteReadRoute, kindReadRoute⟩ := accepted
  have siteReadUnary : UnaryHistory siteRead :=
    unary_cont_closed siteUnary requestedSupplyUnary siteReadRoute
  have kindReadUnary : UnaryHistory kindRead :=
    unary_cont_closed socketKindUnary auditGateUnary kindReadRoute
  subst packetEq
  exact
    ⟨site, requestedSupply, socketKind, auditGate, transport, continuation, provenance,
      localName, rfl, List.Mem.tail site (List.Mem.head _),
      List.Mem.tail site (List.Mem.tail requestedSupply (List.Mem.head _)),
      List.Mem.tail site
        (List.Mem.tail requestedSupply (List.Mem.tail socketKind (List.Mem.head _))),
      siteReadUnary, kindReadUnary⟩

end BEDC.Derived.SocketReportUp
