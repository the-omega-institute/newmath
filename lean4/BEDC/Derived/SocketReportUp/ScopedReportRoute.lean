import BEDC.Derived.SocketReportUp.SiblingSeparation

namespace BEDC.Derived.SocketReportUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SocketReportScopedReportRoute [AskSetup] [PackageSetup]
    {x : SocketReportUp} {siteRead kindRead reportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (∃ site requestedSupply socketKind auditGate transport continuation provenance localName :
      BHist,
      x = SocketReportUp.mk site requestedSupply socketKind auditGate transport continuation
        provenance localName ∧
        UnaryHistory site ∧ UnaryHistory requestedSupply ∧ UnaryHistory socketKind ∧
          UnaryHistory auditGate ∧ UnaryHistory continuation ∧ UnaryHistory localName ∧
            Cont site requestedSupply siteRead ∧ Cont socketKind auditGate kindRead ∧
              Cont continuation localName reportRead ∧ PkgSig bundle reportRead pkg) →
      ∃ site requestedSupply socketKind auditGate transport continuation provenance localName :
        BHist,
        x = SocketReportUp.mk site requestedSupply socketKind auditGate transport continuation
          provenance localName ∧
          List.Mem requestedSupply (socketReportFields x) ∧
            List.Mem socketKind (socketReportFields x) ∧
              List.Mem auditGate (socketReportFields x) ∧
                UnaryHistory siteRead ∧ UnaryHistory kindRead ∧ UnaryHistory reportRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro accepted
  obtain ⟨site, requestedSupply, socketKind, auditGate, transport, continuation,
    provenance, localName, packetEq, siteUnary, requestedSupplyUnary, socketKindUnary,
    auditGateUnary, continuationUnary, localNameUnary, siteRoute, kindRoute, reportRoute,
    _reportPkg⟩ := accepted
  have siteReadUnary : UnaryHistory siteRead :=
    unary_cont_closed siteUnary requestedSupplyUnary siteRoute
  have kindReadUnary : UnaryHistory kindRead :=
    unary_cont_closed socketKindUnary auditGateUnary kindRoute
  have reportReadUnary : UnaryHistory reportRead :=
    unary_cont_closed continuationUnary localNameUnary reportRoute
  cases packetEq
  exact
    ⟨site, requestedSupply, socketKind, auditGate, transport, continuation, provenance,
      localName, rfl, List.Mem.tail site (List.Mem.head _),
      List.Mem.tail site (List.Mem.tail requestedSupply (List.Mem.head _)),
      List.Mem.tail site
        (List.Mem.tail requestedSupply (List.Mem.tail socketKind (List.Mem.head _))),
      siteReadUnary, kindReadUnary, reportReadUnary⟩

end BEDC.Derived.SocketReportUp
