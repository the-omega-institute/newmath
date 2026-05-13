import BEDC.Derived.RegularCauchyDiagonalUp

namespace BEDC.Derived.RegularCauchyDiagonalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyDiagonalCarrier_real_completion_handoff_package [AskSetup] [PackageSetup]
    {ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert selectedWindow
      completionRead sealRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
        provenance localCert bundle pkg ->
      Cont windowLedger streamWindow selectedWindow ->
        Cont selectedWindow regseqRead completionRead ->
          Cont regseqRead realSeal sealRead ->
            Cont sealRead localCert consumerRead ->
              PkgSig bundle completionRead pkg ->
                PkgSig bundle sealRead pkg ->
                  PkgSig bundle consumerRead pkg ->
                    UnaryHistory selectedWindow ∧ UnaryHistory completionRead ∧
                      UnaryHistory sealRead ∧ UnaryHistory consumerRead ∧
                        Cont selectedWindow regseqRead completionRead ∧
                          Cont regseqRead realSeal sealRead ∧
                            Cont sealRead localCert consumerRead ∧
                              hsame windowLedger sealRead ∧ PkgSig bundle provenance pkg ∧
                                PkgSig bundle completionRead pkg ∧
                                  PkgSig bundle sealRead pkg ∧
                                    PkgSig bundle consumerRead pkg := by
  intro carrier windowSelection completionRow sealReadRow consumerRow completionPkg sealReadPkg
    consumerPkg
  have handoff :=
    RegularCauchyDiagonalCarrier_real_completion_handoff carrier windowSelection completionRow
      sealReadRow completionPkg sealReadPkg
  obtain ⟨selectedWindowUnary, completionUnary, sealReadUnary, completionRoute, sealRoute,
    ledgerSameSealRead, provenancePkg, completionPkgOut, sealReadPkgOut⟩ := handoff
  obtain ⟨_ratSeedUnary, _streamWindowUnary, _regseqReadUnary, _realSealUnary,
    _windowLedgerUnary, _provenanceUnary, localCertUnary, _ratStreamRegseq,
    _regseqSealLedger, _sealLocalProvenance, _carrierPkg⟩ := carrier
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed sealReadUnary localCertUnary consumerRow
  exact
    ⟨selectedWindowUnary, completionUnary, sealReadUnary, consumerUnary, completionRoute,
      sealRoute, consumerRow, ledgerSameSealRead, provenancePkg, completionPkgOut,
      sealReadPkgOut, consumerPkg⟩

end BEDC.Derived.RegularCauchyDiagonalUp
