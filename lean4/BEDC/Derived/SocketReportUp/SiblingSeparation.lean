import BEDC.Derived.SocketReportUp.NameCertObligations

namespace BEDC.Derived.SocketReportUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SocketReportUp_sibling_separation [AskSetup] [PackageSetup]
    {x : SocketReportUp} {siteRead kindRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (∃ site requestedSupply socketKind auditGate transport continuation provenance
      localName : BHist,
      x = SocketReportUp.mk site requestedSupply socketKind auditGate transport
        continuation provenance localName ∧
        UnaryHistory site ∧ UnaryHistory requestedSupply ∧ UnaryHistory socketKind ∧
          UnaryHistory auditGate ∧ UnaryHistory continuation ∧ UnaryHistory localName ∧
            Cont site requestedSupply siteRead ∧ Cont socketKind auditGate kindRead ∧
              Cont continuation localName namedRead ∧ PkgSig bundle namedRead pkg) →
      ∃ site requestedSupply socketKind auditGate transport continuation provenance
        localName : BHist,
        x = SocketReportUp.mk site requestedSupply socketKind auditGate transport
          continuation provenance localName ∧
          List.Mem requestedSupply (socketReportFields x) ∧
            List.Mem socketKind (socketReportFields x) ∧
              List.Mem auditGate (socketReportFields x) ∧
                List.Mem continuation (socketReportFields x) ∧
                  List.Mem localName (socketReportFields x) ∧
                    UnaryHistory siteRead ∧ UnaryHistory kindRead ∧
                      UnaryHistory namedRead ∧
                        SemanticNameCert
                          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row siteRead ∨ hsame row kindRead ∨
                              hsame row namedRead)
                          (fun row : BHist =>
                            PkgSig bundle namedRead pkg ∧ hsame row namedRead)
                          hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro accepted
  obtain ⟨site, requestedSupply, socketKind, auditGate, transport, continuation,
    provenance, localName, packetEq, siteUnary, requestedSupplyUnary, socketKindUnary,
    auditGateUnary, continuationUnary, localNameUnary, siteCont, kindCont, namedCont,
    namedPkg⟩ := accepted
  have obligations :=
    SocketReportNameCertObligations
      (site := site) (requestedSupply := requestedSupply) (socketKind := socketKind)
      (auditGate := auditGate) (transport := transport) (continuation := continuation)
      (provenance := provenance) (localName := localName) (siteRead := siteRead)
      (kindRead := kindRead) (namedRead := namedRead) (bundle := bundle) (pkg := pkg)
      siteUnary requestedSupplyUnary socketKindUnary auditGateUnary continuationUnary
      localNameUnary siteCont kindCont namedCont namedPkg
  obtain ⟨_fields, siteReadUnary, kindReadUnary, namedReadUnary, cert⟩ := obligations
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
            (List.Mem.tail auditGate (List.Mem.tail transport (List.Mem.head _))))),
      List.Mem.tail site
        (List.Mem.tail requestedSupply
          (List.Mem.tail socketKind
            (List.Mem.tail auditGate
              (List.Mem.tail transport
                (List.Mem.tail continuation
                  (List.Mem.tail provenance (List.Mem.head _))))))),
      siteReadUnary, kindReadUnary, namedReadUnary, cert⟩

end BEDC.Derived.SocketReportUp
