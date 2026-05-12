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

end BEDC.Derived.ObserverHistIdentityUp
