import BEDC.Derived.RegularCauchyDiagonalUp.MatureConsumerExhaustion

namespace BEDC.Derived.RegularCauchyDiagonalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyDiagonalCarrier_mature_closure_certificate [AskSetup] [PackageSetup]
    {ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert
      selectedWindow completionRead sealRead endpoint : BHist}
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
                    SemanticNameCert
                        (fun row : BHist =>
                          hsame row realSeal ∧
                            RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead
                              realSeal windowLedger provenance localCert bundle pkg)
                        (fun row : BHist => hsame row realSeal ∧ UnaryHistory windowLedger)
                        (fun row : BHist => hsame row realSeal ∧ PkgSig bundle provenance pkg)
                        hsame ∧
                      UnaryHistory completionRead ∧ UnaryHistory sealRead ∧
                        UnaryHistory endpoint ∧ hsame windowLedger sealRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle completionRead pkg ∧
                            PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont NameCert
  intro carrier windowSelection completionRow sealReadRow endpointRow completionPkg sealReadPkg
    endpointPkg
  have nameSurface :=
    RegularCauchyDiagonalCarrier_namecert_obligations carrier
  obtain ⟨cert, _ratSeedUnary, _streamWindowUnary, _regseqReadUnary, _realSealUnary,
    _windowLedgerUnary, _provenancePkgFromCert⟩ := nameSurface
  have consumers :=
    RegularCauchyDiagonalCarrier_mature_consumer_exhaustion carrier windowSelection completionRow
      sealReadRow endpointRow completionPkg sealReadPkg endpointPkg
  obtain ⟨_selectedWindowUnary, completionUnary, sealReadUnary, endpointUnary,
    _completionRoute, _sealRoute, _endpointRoute, ledgerSameSeal, provenancePkg,
    completionPkgOut, _sealReadPkgOut, endpointPkgOut⟩ := consumers
  exact
    ⟨cert, completionUnary, sealReadUnary, endpointUnary, ledgerSameSeal, provenancePkg,
      completionPkgOut, endpointPkgOut⟩

end BEDC.Derived.RegularCauchyDiagonalUp
