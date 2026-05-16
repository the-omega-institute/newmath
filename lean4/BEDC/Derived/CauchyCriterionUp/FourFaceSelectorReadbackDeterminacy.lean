import BEDC.Derived.CauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem CauchyCriterionCarrier_four_face_selector_readback_determinacy
    [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      request0 request1 readback0 readback1 : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      Cont window endpoint request0 ->
        Cont window endpoint request1 ->
          Cont request0 realSeal readback0 ->
            Cont request1 realSeal readback1 ->
              PkgSig bundle readback0 pkg ->
                PkgSig bundle readback1 pkg ->
                  hsame request0 request1 ∧ hsame readback0 readback1 ∧
                    PkgSig bundle endpoint pkg ∧ PkgSig bundle readback0 pkg ∧
                      PkgSig bundle readback1 pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier requestRoute0 requestRoute1 readbackRoute0 readbackRoute1 readbackPkg0
    readbackPkg1
  rcases carrier with
    ⟨_windowUnary, _modulusUnary, _toleranceUnary, _ledgerUnary, _regseqUnary,
      _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
      _endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq,
      _regseqRealSealTransport, _transportLocalCertRoute, _routeProvenanceEndpoint,
      endpointPkg⟩
  have sameRequest : hsame request0 request1 :=
    cont_deterministic requestRoute0 requestRoute1
  have sameReadback : hsame readback0 readback1 :=
    cont_respects_hsame sameRequest (hsame_refl realSeal) readbackRoute0 readbackRoute1
  exact ⟨sameRequest, sameReadback, endpointPkg, readbackPkg0, readbackPkg1⟩

end BEDC.Derived.CauchyCriterionUp
