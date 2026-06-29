import BEDC.Derived.SocketReportUp.ScopedReportRoute

namespace BEDC.Derived.SocketReportUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SocketReportPublicExportSurface [AskSetup] [PackageSetup]
    {x : SocketReportUp} {siteRead kindRead reportRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (∃ site requestedSupply socketKind auditGate transport continuation provenance
      localName : BHist,
      x = SocketReportUp.mk site requestedSupply socketKind auditGate transport
        continuation provenance localName ∧
        UnaryHistory site ∧ UnaryHistory requestedSupply ∧ UnaryHistory socketKind ∧
          UnaryHistory auditGate ∧ UnaryHistory transport ∧ UnaryHistory continuation ∧
            UnaryHistory provenance ∧ UnaryHistory localName ∧
              Cont site requestedSupply siteRead ∧ Cont socketKind auditGate kindRead ∧
                Cont continuation localName reportRead ∧
                  Cont reportRead provenance publicRead ∧
                    PkgSig bundle publicRead pkg) →
      ∃ site requestedSupply socketKind auditGate transport continuation provenance
        localName : BHist,
        x = SocketReportUp.mk site requestedSupply socketKind auditGate transport
          continuation provenance localName ∧
          List.Mem requestedSupply (socketReportFields x) ∧
            List.Mem socketKind (socketReportFields x) ∧
              List.Mem auditGate (socketReportFields x) ∧
                List.Mem transport (socketReportFields x) ∧
                  List.Mem continuation (socketReportFields x) ∧
                    List.Mem provenance (socketReportFields x) ∧
                      List.Mem localName (socketReportFields x) ∧
                        UnaryHistory siteRead ∧ UnaryHistory kindRead ∧
                          UnaryHistory reportRead ∧ UnaryHistory publicRead ∧
                            PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro accepted
  obtain ⟨site, requestedSupply, socketKind, auditGate, transport, continuation,
    provenance, localName, packetEq, siteUnary, requestedSupplyUnary, socketKindUnary,
    auditGateUnary, _transportUnary, continuationUnary, provenanceUnary, localNameUnary,
    siteRoute, kindRoute, reportRoute, publicRoute, publicPkg⟩ := accepted
  have siteReadUnary : UnaryHistory siteRead :=
    unary_cont_closed siteUnary requestedSupplyUnary siteRoute
  have kindReadUnary : UnaryHistory kindRead :=
    unary_cont_closed socketKindUnary auditGateUnary kindRoute
  have reportReadUnary : UnaryHistory reportRead :=
    unary_cont_closed continuationUnary localNameUnary reportRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed reportReadUnary provenanceUnary publicRoute
  cases packetEq
  exact
    ⟨site, requestedSupply, socketKind, auditGate, transport, continuation, provenance,
      localName, rfl, List.Mem.tail site (List.Mem.head _),
      List.Mem.tail site (List.Mem.tail requestedSupply (List.Mem.head _)),
      List.Mem.tail site
        (List.Mem.tail requestedSupply (List.Mem.tail socketKind (List.Mem.head _))),
      List.Mem.tail site
        (List.Mem.tail requestedSupply
          (List.Mem.tail socketKind
            (List.Mem.tail auditGate (List.Mem.head _)))),
      List.Mem.tail site
        (List.Mem.tail requestedSupply
          (List.Mem.tail socketKind
            (List.Mem.tail auditGate (List.Mem.tail transport (List.Mem.head _))))),
      List.Mem.tail site
        (List.Mem.tail requestedSupply
          (List.Mem.tail socketKind
            (List.Mem.tail auditGate
              (List.Mem.tail transport
                (List.Mem.tail continuation (List.Mem.head _)))))),
      List.Mem.tail site
        (List.Mem.tail requestedSupply
          (List.Mem.tail socketKind
            (List.Mem.tail auditGate
              (List.Mem.tail transport
                (List.Mem.tail continuation
                  (List.Mem.tail provenance (List.Mem.head _))))))),
      siteReadUnary, kindReadUnary, reportReadUnary, publicReadUnary, publicPkg⟩

end BEDC.Derived.SocketReportUp
