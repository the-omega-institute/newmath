import BEDC.Derived.RegularCauchyDiagonalUp

namespace BEDC.Derived.RegularCauchyDiagonalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyDiagonalCarrier_mature_consumer_exhaustion [AskSetup] [PackageSetup]
    {ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert selectedWindow
      completionRead sealRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
        provenance localCert bundle pkg ->
      Cont windowLedger streamWindow selectedWindow ->
        Cont selectedWindow regseqRead completionRead ->
          Cont regseqRead realSeal sealRead ->
            Cont realSeal provenance endpoint ->
              PkgSig bundle completionRead pkg ->
                PkgSig bundle sealRead pkg ->
                  PkgSig bundle endpoint pkg ->
                    UnaryHistory selectedWindow ∧ UnaryHistory completionRead ∧
                      UnaryHistory sealRead ∧ UnaryHistory endpoint ∧
                        Cont selectedWindow regseqRead completionRead ∧
                          Cont regseqRead realSeal sealRead ∧
                            Cont realSeal provenance endpoint ∧ hsame windowLedger sealRead ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle completionRead pkg ∧
                                  PkgSig bundle sealRead pkg ∧
                                    PkgSig bundle endpoint pkg := by
  intro carrier windowSelection completionRow sealReadRow endpointRow completionPkg sealReadPkg
    endpointPkg
  have handoff :=
    RegularCauchyDiagonalCarrier_real_completion_handoff carrier windowSelection completionRow
      sealReadRow completionPkg sealReadPkg
  obtain ⟨selectedWindowUnary, completionUnary, sealReadUnary, completionRoute, sealRoute,
    ledgerSameSeal, provenancePkg, completionPkgOut, sealReadPkgOut⟩ := handoff
  obtain ⟨_ratSeedUnary, _streamWindowUnary, _regseqReadUnary, realSealUnary,
    _windowLedgerUnary, provenanceUnary, _localCertUnary, _ratStreamRegseq,
    _regseqSealLedger, _sealLocalProvenance, _carrierPkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed realSealUnary provenanceUnary endpointRow
  exact
    ⟨selectedWindowUnary, completionUnary, sealReadUnary, endpointUnary, completionRoute,
      sealRoute, endpointRow, ledgerSameSeal, provenancePkg, completionPkgOut,
      sealReadPkgOut, endpointPkg⟩

end BEDC.Derived.RegularCauchyDiagonalUp
