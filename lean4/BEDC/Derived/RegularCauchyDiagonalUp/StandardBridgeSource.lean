import BEDC.Derived.RegularCauchyDiagonalUp

namespace BEDC.Derived.RegularCauchyDiagonalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyDiagonalCarrier_standard_bridge_source [AskSetup] [PackageSetup]
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
                  UnaryHistory ratSeed ∧ UnaryHistory streamWindow ∧
                    UnaryHistory regseqRead ∧ UnaryHistory realSeal ∧
                      UnaryHistory windowLedger ∧ UnaryHistory selectedWindow ∧
                        UnaryHistory sealRead ∧ UnaryHistory completionRead ∧
                          Cont windowLedger streamWindow selectedWindow ∧
                            Cont regseqRead realSeal sealRead ∧
                              Cont selectedWindow regseqRead completionRead ∧
                                hsame windowLedger sealRead ∧ PkgSig bundle provenance pkg ∧
                                  PkgSig bundle selectedWindow pkg ∧ PkgSig bundle sealRead pkg ∧
                                    PkgSig bundle completionRead pkg := by
  intro carrier windowSelection sealReadRow completionReadRow selectedPkg sealReadPkg
    completionReadPkg
  obtain ⟨ratSeedUnary, streamWindowUnary, regseqReadUnary, realSealUnary,
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
    ⟨ratSeedUnary, streamWindowUnary, regseqReadUnary, realSealUnary, windowLedgerUnary,
      selectedWindowUnary, sealReadUnary, completionReadUnary, windowSelection, sealReadRow,
      completionReadRow, ledgerSameSealRead, provenancePkg, selectedPkg, sealReadPkg,
      completionReadPkg⟩

end BEDC.Derived.RegularCauchyDiagonalUp
