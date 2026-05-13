import BEDC.Derived.RegularCauchyDiagonalUp.RootSourceDeterminacy

namespace BEDC.Derived.RegularCauchyDiagonalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyDiagonalCarrier_root_window_ledger_exactness [AskSetup] [PackageSetup]
    {ratSeed streamWindow regseqRead regseqRead' realSeal windowLedger windowLedger'
      provenance provenance' localCert selectedWindow consumerSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
        provenance localCert bundle pkg ->
      RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead' realSeal windowLedger'
          provenance' localCert bundle pkg ->
        Cont windowLedger' streamWindow selectedWindow ->
          Cont regseqRead' realSeal consumerSeal ->
            PkgSig bundle selectedWindow pkg ->
              hsame regseqRead regseqRead' ∧ hsame windowLedger windowLedger' ∧
                hsame provenance provenance' ∧ hsame windowLedger' consumerSeal ∧
                  UnaryHistory selectedWindow ∧ UnaryHistory consumerSeal ∧
                    PkgSig bundle provenance' pkg ∧ PkgSig bundle selectedWindow pkg := by
  intro leftCarrier rightCarrier windowSelection consumerSealRow selectedPkg
  have rootSame :=
    RegularCauchyDiagonalCarrier_root_source_determinacy leftCarrier rightCarrier
  obtain ⟨regseqSame, windowLedgerSame, provenanceSame⟩ := rootSame
  obtain ⟨_ratSeedUnary, streamWindowUnary, regseqReadUnary, realSealUnary,
    windowLedgerUnary, _provenanceUnary, _localCertUnary, _ratStreamRegseq,
    regseqSealLedger, _sealLocalProvenance, provenancePkg⟩ := rightCarrier
  have selectedWindowUnary : UnaryHistory selectedWindow :=
    unary_cont_closed windowLedgerUnary streamWindowUnary windowSelection
  have consumerSealUnary : UnaryHistory consumerSeal :=
    unary_cont_closed regseqReadUnary realSealUnary consumerSealRow
  have ledgerSameConsumer : hsame windowLedger' consumerSeal :=
    cont_deterministic regseqSealLedger consumerSealRow
  exact
    ⟨regseqSame, windowLedgerSame, provenanceSame, ledgerSameConsumer, selectedWindowUnary,
      consumerSealUnary, provenancePkg, selectedPkg⟩

end BEDC.Derived.RegularCauchyDiagonalUp
