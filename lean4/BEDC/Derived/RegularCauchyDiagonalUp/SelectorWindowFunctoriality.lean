import BEDC.Derived.RegularCauchyDiagonalUp

namespace BEDC.Derived.RegularCauchyDiagonalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyDiagonalCarrier_selector_window_functoriality [AskSetup] [PackageSetup]
    {ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert ratSeed'
      streamWindow' regseqRead' realSeal' windowLedger' provenance' localCert'
      selectedWindow selectedWindow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
        provenance localCert bundle pkg ->
      hsame ratSeed ratSeed' ->
        hsame streamWindow streamWindow' ->
          hsame realSeal realSeal' ->
            hsame localCert localCert' ->
              Cont ratSeed' streamWindow' regseqRead' ->
                Cont regseqRead' realSeal' windowLedger' ->
                  Cont realSeal' localCert' provenance' ->
                    PkgSig bundle provenance' pkg ->
                      Cont windowLedger streamWindow selectedWindow ->
                        Cont windowLedger' streamWindow' selectedWindow' ->
                          PkgSig bundle selectedWindow' pkg ->
                            RegularCauchyDiagonalCarrier ratSeed' streamWindow' regseqRead'
                                realSeal' windowLedger' provenance' localCert' bundle pkg ∧
                              hsame selectedWindow selectedWindow' ∧
                                UnaryHistory selectedWindow ∧ UnaryHistory selectedWindow' ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle provenance' pkg ∧
                                      PkgSig bundle selectedWindow' pkg := by
  intro carrier ratSeedSame streamWindowSame realSealSame localCertSame regseqReadRow
    windowLedgerRow provenanceRow provenancePkg' selectedWindowRow selectedWindowRow'
    selectedWindowPkg'
  obtain ⟨ratSeedUnary, streamWindowUnary, _regseqReadUnary, realSealUnary,
    windowLedgerUnary, _provenanceUnary, localCertUnary, ratStreamRegseq,
    regseqSealLedger, sealLocalProvenance, provenancePkg⟩ := carrier
  have ratSeedUnary' : UnaryHistory ratSeed' :=
    unary_transport ratSeedUnary ratSeedSame
  have streamWindowUnary' : UnaryHistory streamWindow' :=
    unary_transport streamWindowUnary streamWindowSame
  have regseqReadUnary' : UnaryHistory regseqRead' :=
    unary_cont_closed ratSeedUnary' streamWindowUnary' regseqReadRow
  have realSealUnary' : UnaryHistory realSeal' :=
    unary_transport realSealUnary realSealSame
  have windowLedgerUnary' : UnaryHistory windowLedger' :=
    unary_cont_closed regseqReadUnary' realSealUnary' windowLedgerRow
  have localCertUnary' : UnaryHistory localCert' :=
    unary_transport localCertUnary localCertSame
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed realSealUnary' localCertUnary' provenanceRow
  have regseqReadSame : hsame regseqRead regseqRead' :=
    cont_respects_hsame ratSeedSame streamWindowSame ratStreamRegseq regseqReadRow
  have windowLedgerSame : hsame windowLedger windowLedger' :=
    cont_respects_hsame regseqReadSame realSealSame regseqSealLedger windowLedgerRow
  have provenanceSame : hsame provenance provenance' :=
    cont_respects_hsame realSealSame localCertSame sealLocalProvenance provenanceRow
  have selectedWindowSame : hsame selectedWindow selectedWindow' :=
    cont_respects_hsame windowLedgerSame streamWindowSame selectedWindowRow
      selectedWindowRow'
  have selectedWindowUnary : UnaryHistory selectedWindow :=
    unary_cont_closed windowLedgerUnary streamWindowUnary selectedWindowRow
  have selectedWindowUnary' : UnaryHistory selectedWindow' :=
    unary_cont_closed windowLedgerUnary' streamWindowUnary' selectedWindowRow'
  exact
    ⟨⟨ratSeedUnary', streamWindowUnary', regseqReadUnary', realSealUnary',
      windowLedgerUnary', provenanceUnary', localCertUnary', regseqReadRow, windowLedgerRow,
      provenanceRow, provenancePkg'⟩, selectedWindowSame, selectedWindowUnary,
      selectedWindowUnary', provenancePkg, provenancePkg', selectedWindowPkg'⟩

end BEDC.Derived.RegularCauchyDiagonalUp
