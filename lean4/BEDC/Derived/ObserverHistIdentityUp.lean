import BEDC.Derived.ObserverHistoryIdentityUp

namespace BEDC.Derived.ObserverHistIdentityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem ObserverHistoryIdentityPacket_transport_stability [AskSetup] [PackageSetup]
    {leftHistory rightHistory signatures samenessRows ledger routes provenance nameCert
      nameCert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (packet :
      BEDC.Derived.ObserverHistoryIdentityUp.ObserverHistoryIdentityPacket leftHistory
        rightHistory signatures samenessRows ledger routes provenance nameCert bundle pkg)
    (sameName : hsame nameCert nameCert') :
    BEDC.Derived.ObserverHistoryIdentityUp.ObserverHistoryIdentityPacket leftHistory
        rightHistory signatures samenessRows ledger routes provenance nameCert' bundle pkg ∧
      SameSig bundle leftHistory rightHistory ∧ Cont ledger routes samenessRows := by
  obtain ⟨leftUnary, rightUnary, signaturesUnary, samenessRowsUnary, ledgerUnary, routesUnary,
    provenanceUnary, nameCertUnary, sameRows, ledgerRoutes, provenancePkg, signaturesPkg⟩ :=
      packet
  exact
    ⟨⟨leftUnary, rightUnary, signaturesUnary, samenessRowsUnary, ledgerUnary, routesUnary,
      provenanceUnary, unary_transport nameCertUnary sameName, sameRows, ledgerRoutes,
      provenancePkg, signaturesPkg⟩, sameRows, ledgerRoutes⟩

theorem ObserverHistIdentityPacket_consumer_surface [AskSetup] [PackageSetup]
    {leftHistory rightHistory signatures samenessRows ledger routes provenance nameCert
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.ObserverHistoryIdentityUp.ObserverHistoryIdentityPacket leftHistory
        rightHistory signatures samenessRows ledger routes provenance nameCert bundle pkg ->
      Cont samenessRows nameCert endpoint ->
        PkgSig bundle endpoint pkg ->
          BEDC.Derived.ObserverHistoryIdentityUp.ObserverHistoryIdentityPacket leftHistory
              rightHistory signatures samenessRows ledger routes provenance nameCert bundle pkg ∧
            SameSig bundle leftHistory rightHistory ∧ Cont ledger routes samenessRows ∧
              UnaryHistory endpoint ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg
  intro packet samenessEndpoint endpointPkg
  have packetWitness := packet
  obtain ⟨_leftUnary, _rightUnary, _signaturesUnary, samenessRowsUnary, _ledgerUnary,
    _routesUnary, _provenanceUnary, nameCertUnary, sameRows, ledgerRoutes, _provenancePkg,
    _signaturesPkg⟩ := packet
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed samenessRowsUnary nameCertUnary samenessEndpoint
  exact ⟨packetWitness, sameRows, ledgerRoutes, endpointUnary, endpointPkg⟩

end BEDC.Derived.ObserverHistIdentityUp
