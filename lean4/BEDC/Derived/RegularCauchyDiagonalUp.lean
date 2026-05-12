import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyDiagonalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyDiagonalCarrier [AskSetup] [PackageSetup]
    (ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory ratSeed ∧ UnaryHistory streamWindow ∧ UnaryHistory regseqRead ∧
    UnaryHistory realSeal ∧ UnaryHistory windowLedger ∧ UnaryHistory provenance ∧
      UnaryHistory localCert ∧ Cont ratSeed streamWindow regseqRead ∧
        Cont regseqRead realSeal windowLedger ∧ Cont realSeal localCert provenance ∧
          PkgSig bundle provenance pkg

theorem RegularCauchyDiagonalCarrier_window_coverage [AskSetup] [PackageSetup]
    {ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert
      selectedWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
        provenance localCert bundle pkg ->
      Cont windowLedger streamWindow selectedWindow ->
        PkgSig bundle selectedWindow pkg ->
          UnaryHistory ratSeed ∧ UnaryHistory streamWindow ∧ UnaryHistory regseqRead ∧
            UnaryHistory selectedWindow ∧ Cont windowLedger streamWindow selectedWindow ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle selectedWindow pkg := by
  intro carrier windowSelection selectedPkg
  obtain ⟨ratSeedUnary, streamWindowUnary, regseqReadUnary, _realSealUnary,
    windowLedgerUnary, _provenanceUnary, _localCertUnary, _ratStreamRegseq,
    _regseqSealLedger, _sealLocalProvenance, provenancePkg⟩ := carrier
  have selectedWindowUnary : UnaryHistory selectedWindow :=
    unary_cont_closed windowLedgerUnary streamWindowUnary windowSelection
  exact
    ⟨ratSeedUnary, streamWindowUnary, regseqReadUnary, selectedWindowUnary,
      windowSelection, provenancePkg, selectedPkg⟩

theorem RegularCauchyDiagonalCarrier_source_stability_obligation [AskSetup] [PackageSetup]
    {ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert ratSeed'
      streamWindow' regseqRead' realSeal' windowLedger' provenance' localCert' : BHist}
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
                      RegularCauchyDiagonalCarrier ratSeed' streamWindow' regseqRead'
                          realSeal' windowLedger' provenance' localCert' bundle pkg ∧
                        hsame regseqRead regseqRead' ∧ hsame windowLedger windowLedger' ∧
                          hsame provenance provenance' := by
  intro carrier ratSeedSame streamWindowSame realSealSame localCertSame ratStreamRow
    regseqSealRow sealLocalRow pkgSig
  obtain ⟨ratSeedUnary, streamWindowUnary, _regseqReadUnary, realSealUnary,
    _windowLedgerUnary, _provenanceUnary, localCertUnary, carrierRatStreamRow,
    carrierRegseqSealRow, carrierSealLocalRow, _carrierPkgSig⟩ := carrier
  have ratSeedUnary' : UnaryHistory ratSeed' :=
    unary_transport ratSeedUnary ratSeedSame
  have streamWindowUnary' : UnaryHistory streamWindow' :=
    unary_transport streamWindowUnary streamWindowSame
  have regseqReadUnary' : UnaryHistory regseqRead' :=
    unary_cont_closed ratSeedUnary' streamWindowUnary' ratStreamRow
  have realSealUnary' : UnaryHistory realSeal' :=
    unary_transport realSealUnary realSealSame
  have windowLedgerUnary' : UnaryHistory windowLedger' :=
    unary_cont_closed regseqReadUnary' realSealUnary' regseqSealRow
  have localCertUnary' : UnaryHistory localCert' :=
    unary_transport localCertUnary localCertSame
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed realSealUnary' localCertUnary' sealLocalRow
  have regseqSame : hsame regseqRead regseqRead' :=
    cont_respects_hsame ratSeedSame streamWindowSame carrierRatStreamRow ratStreamRow
  have windowLedgerSame : hsame windowLedger windowLedger' :=
    cont_respects_hsame regseqSame realSealSame carrierRegseqSealRow regseqSealRow
  have provenanceSame : hsame provenance provenance' :=
    cont_respects_hsame realSealSame localCertSame carrierSealLocalRow sealLocalRow
  exact
    ⟨⟨ratSeedUnary', streamWindowUnary', regseqReadUnary', realSealUnary',
      windowLedgerUnary', provenanceUnary', localCertUnary', ratStreamRow, regseqSealRow,
      sealLocalRow, pkgSig⟩, regseqSame, windowLedgerSame, provenanceSame⟩

end BEDC.Derived.RegularCauchyDiagonalUp
