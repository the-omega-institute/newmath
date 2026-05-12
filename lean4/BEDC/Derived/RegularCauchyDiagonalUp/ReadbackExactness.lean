import BEDC.Derived.RegularCauchyDiagonalUp

namespace BEDC.Derived.RegularCauchyDiagonalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyDiagonalCarrier_bridge_readback_exactness [AskSetup] [PackageSetup]
    {ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert selectedWindow
      sealRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
        provenance localCert bundle pkg ->
      Cont windowLedger streamWindow selectedWindow ->
        Cont regseqRead realSeal sealRead ->
          Cont selectedWindow regseqRead completionRead ->
            PkgSig bundle selectedWindow pkg ->
              PkgSig bundle sealRead pkg ->
                PkgSig bundle completionRead pkg ->
                  hsame windowLedger sealRead ∧ UnaryHistory selectedWindow ∧
                    UnaryHistory sealRead ∧ UnaryHistory completionRead ∧
                      Cont windowLedger streamWindow selectedWindow ∧
                        Cont selectedWindow regseqRead completionRead ∧
                          PkgSig bundle provenance pkg ∧
                            PkgSig bundle completionRead pkg := by
  intro carrier windowSelection sealReadRow completionReadRow _selectedPkg _sealReadPkg
    completionReadPkg
  obtain ⟨_ratSeedUnary, streamWindowUnary, regseqReadUnary, realSealUnary,
    windowLedgerUnary, _provenanceUnary, _localCertUnary, _ratStreamRegseq,
    regseqSealLedger, _sealLocalProvenance, provenancePkg⟩ := carrier
  have selectedWindowUnary : UnaryHistory selectedWindow :=
    unary_cont_closed windowLedgerUnary streamWindowUnary windowSelection
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regseqReadUnary realSealUnary sealReadRow
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed selectedWindowUnary regseqReadUnary completionReadRow
  have ledgerSameSealRead : hsame windowLedger sealRead :=
    cont_deterministic regseqSealLedger sealReadRow
  exact
    ⟨ledgerSameSealRead, selectedWindowUnary, sealReadUnary, completionReadUnary,
      windowSelection, completionReadRow, provenancePkg, completionReadPkg⟩

end BEDC.Derived.RegularCauchyDiagonalUp
