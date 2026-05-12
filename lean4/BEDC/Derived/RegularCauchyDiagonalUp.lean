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

theorem RegularCauchyDiagonalCarrier_real_seal_handoff [AskSetup] [PackageSetup]
    {ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert
      selectedWindow consumerSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
        provenance localCert bundle pkg ->
      Cont windowLedger streamWindow selectedWindow ->
        Cont regseqRead realSeal consumerSeal ->
          UnaryHistory ratSeed ∧ UnaryHistory streamWindow ∧ UnaryHistory regseqRead ∧
            UnaryHistory realSeal ∧ UnaryHistory windowLedger ∧ UnaryHistory selectedWindow ∧
              UnaryHistory consumerSeal ∧ Cont ratSeed streamWindow regseqRead ∧
                Cont regseqRead realSeal windowLedger ∧ Cont regseqRead realSeal consumerSeal ∧
                  hsame windowLedger consumerSeal ∧ PkgSig bundle provenance pkg := by
  intro carrier windowSelection consumerSealRow
  obtain ⟨ratSeedUnary, streamWindowUnary, regseqReadUnary, realSealUnary,
    windowLedgerUnary, _provenanceUnary, _localCertUnary, ratStreamRegseq,
    regseqSealLedger, _sealLocalProvenance, provenancePkg⟩ := carrier
  have selectedWindowUnary : UnaryHistory selectedWindow :=
    unary_cont_closed windowLedgerUnary streamWindowUnary windowSelection
  have consumerSealUnary : UnaryHistory consumerSeal :=
    unary_cont_closed regseqReadUnary realSealUnary consumerSealRow
  have ledgerSameConsumer : hsame windowLedger consumerSeal :=
    cont_deterministic regseqSealLedger consumerSealRow
  exact
    ⟨ratSeedUnary, streamWindowUnary, regseqReadUnary, realSealUnary,
      windowLedgerUnary, selectedWindowUnary, consumerSealUnary, ratStreamRegseq,
      regseqSealLedger, consumerSealRow, ledgerSameConsumer, provenancePkg⟩

theorem RegularCauchyDiagonalCarrier_completion_consumer_bridge [AskSetup] [PackageSetup]
    {ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert selectedWindow
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
        provenance localCert bundle pkg ->
      Cont windowLedger streamWindow selectedWindow ->
        Cont selectedWindow regseqRead completionRead ->
          PkgSig bundle completionRead pkg ->
            UnaryHistory ratSeed ∧ UnaryHistory streamWindow ∧ UnaryHistory regseqRead ∧
              UnaryHistory selectedWindow ∧ UnaryHistory completionRead ∧
                Cont windowLedger streamWindow selectedWindow ∧
                  Cont selectedWindow regseqRead completionRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle completionRead pkg := by
  intro carrier windowSelection completionRow completionPkg
  obtain ⟨ratSeedUnary, streamWindowUnary, regseqReadUnary, _realSealUnary,
    windowLedgerUnary, _provenanceUnary, _localCertUnary, _ratStreamRegseq,
    _regseqSealLedger, _sealLocalProvenance, provenancePkg⟩ := carrier
  have selectedWindowUnary : UnaryHistory selectedWindow :=
    unary_cont_closed windowLedgerUnary streamWindowUnary windowSelection
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed selectedWindowUnary regseqReadUnary completionRow
  exact
    ⟨ratSeedUnary, streamWindowUnary, regseqReadUnary, selectedWindowUnary,
      completionUnary, windowSelection, completionRow, provenancePkg, completionPkg⟩

theorem RegularCauchyDiagonalCarrier_selector_stability [AskSetup] [PackageSetup]
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
                      RegularCauchyDiagonalCarrier ratSeed' streamWindow' regseqRead' realSeal'
                          windowLedger' provenance' localCert' bundle pkg ∧
                        hsame regseqRead regseqRead' ∧ hsame windowLedger windowLedger' ∧
                          hsame provenance provenance' := by
  intro carrier sameRatSeed sameStreamWindow sameRealSeal sameLocalCert regseqReadCont'
    windowLedgerCont' provenanceCont' pkgSig'
  obtain ⟨ratSeedUnary, streamWindowUnary, regseqReadUnary, realSealUnary, _windowLedgerUnary,
    provenanceUnary, localCertUnary, regseqReadCont, windowLedgerCont, provenanceCont,
    _pkgSig⟩ := carrier
  have ratSeedUnary' : UnaryHistory ratSeed' :=
    unary_transport ratSeedUnary sameRatSeed
  have streamWindowUnary' : UnaryHistory streamWindow' :=
    unary_transport streamWindowUnary sameStreamWindow
  have regseqReadUnary' : UnaryHistory regseqRead' :=
    unary_cont_closed ratSeedUnary' streamWindowUnary' regseqReadCont'
  have realSealUnary' : UnaryHistory realSeal' :=
    unary_transport realSealUnary sameRealSeal
  have windowLedgerUnary' : UnaryHistory windowLedger' :=
    unary_cont_closed regseqReadUnary' realSealUnary' windowLedgerCont'
  have localCertUnary' : UnaryHistory localCert' :=
    unary_transport localCertUnary sameLocalCert
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed realSealUnary' localCertUnary' provenanceCont'
  have sameRegseqRead : hsame regseqRead regseqRead' :=
    cont_respects_hsame sameRatSeed sameStreamWindow regseqReadCont regseqReadCont'
  have sameWindowLedger : hsame windowLedger windowLedger' :=
    cont_respects_hsame sameRegseqRead sameRealSeal windowLedgerCont windowLedgerCont'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameRealSeal sameLocalCert provenanceCont provenanceCont'
  have rebuilt :
      RegularCauchyDiagonalCarrier ratSeed' streamWindow' regseqRead' realSeal'
          windowLedger' provenance' localCert' bundle pkg :=
    ⟨ratSeedUnary',
      streamWindowUnary',
      regseqReadUnary',
      realSealUnary',
      windowLedgerUnary',
      provenanceUnary',
      localCertUnary',
      regseqReadCont',
      windowLedgerCont',
      provenanceCont',
      pkgSig'⟩
  exact ⟨rebuilt, sameRegseqRead, sameWindowLedger, sameProvenance⟩

end BEDC.Derived.RegularCauchyDiagonalUp
