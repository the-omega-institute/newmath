import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyDiagonalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem RegularCauchyDiagonalCarrier_stationary_compatibility [AskSetup] [PackageSetup]
    {ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert
      constantSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
        provenance localCert bundle pkg ->
      Cont ratSeed streamWindow regseqRead ->
        Cont regseqRead realSeal constantSeal ->
          PkgSig bundle constantSeal pkg ->
            UnaryHistory ratSeed ∧ UnaryHistory streamWindow ∧ UnaryHistory regseqRead ∧
              UnaryHistory realSeal ∧ UnaryHistory constantSeal ∧
                Cont ratSeed streamWindow regseqRead ∧
                  Cont regseqRead realSeal constantSeal ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle constantSeal pkg := by
  intro carrier stationaryRead constantSealRow constantSealPkg
  obtain ⟨ratSeedUnary, streamWindowUnary, regseqReadUnary, realSealUnary,
    _windowLedgerUnary, _provenanceUnary, _localCertUnary, _ratStreamRegseq,
    _regseqSealLedger, _sealLocalProvenance, provenancePkg⟩ := carrier
  have constantSealUnary : UnaryHistory constantSeal :=
    unary_cont_closed regseqReadUnary realSealUnary constantSealRow
  exact
    ⟨ratSeedUnary, streamWindowUnary, regseqReadUnary, realSealUnary, constantSealUnary,
      stationaryRead, constantSealRow, provenancePkg, constantSealPkg⟩

theorem RegularCauchyDiagonalCarrier_zero_seed [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PkgSig bundle BHist.Empty pkg ->
      RegularCauchyDiagonalCarrier BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty bundle pkg := by
  intro emptyPkg
  exact
    ⟨unary_empty, unary_empty, unary_empty, unary_empty, unary_empty, unary_empty,
      unary_empty, cont_left_unit BHist.Empty, cont_left_unit BHist.Empty,
      cont_left_unit BHist.Empty, emptyPkg⟩

theorem RegularCauchyDiagonalCarrier_stationary_seal_exactness [AskSetup] [PackageSetup]
    {ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert
      constantRead constantSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
        provenance localCert bundle pkg ->
      Cont ratSeed streamWindow constantRead ->
        Cont constantRead realSeal constantSeal ->
          PkgSig bundle constantSeal pkg ->
            hsame regseqRead constantRead ∧ hsame windowLedger constantSeal ∧
              UnaryHistory constantSeal ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle constantSeal pkg := by
  intro carrier stationaryRead stationarySeal constantSealPkg
  obtain ⟨ratSeedUnary, streamWindowUnary, _regseqReadUnary, realSealUnary,
    _windowLedgerUnary, _provenanceUnary, _localCertUnary, ratStreamRegseq,
    regseqSealLedger, _sealLocalProvenance, provenancePkg⟩ := carrier
  have regseqSameConstant : hsame regseqRead constantRead :=
    cont_deterministic ratStreamRegseq stationaryRead
  have windowLedgerSameSeal : hsame windowLedger constantSeal :=
    cont_respects_hsame regseqSameConstant (hsame_refl realSeal) regseqSealLedger
      stationarySeal
  have constantReadUnary : UnaryHistory constantRead :=
    unary_cont_closed ratSeedUnary streamWindowUnary stationaryRead
  have constantSealUnary : UnaryHistory constantSeal :=
    unary_cont_closed constantReadUnary realSealUnary stationarySeal
  exact
    ⟨regseqSameConstant, windowLedgerSameSeal, constantSealUnary, provenancePkg,
      constantSealPkg⟩

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

theorem RegularCauchyDiagonalCarrier_window_ledger_exactness [AskSetup] [PackageSetup]
    {ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert
      selectedWindow consumerSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
        provenance localCert bundle pkg ->
      Cont windowLedger streamWindow selectedWindow ->
        Cont regseqRead realSeal consumerSeal ->
          PkgSig bundle selectedWindow pkg ->
            UnaryHistory ratSeed ∧ UnaryHistory streamWindow ∧ UnaryHistory regseqRead ∧
              UnaryHistory windowLedger ∧ UnaryHistory selectedWindow ∧
                UnaryHistory consumerSeal ∧ Cont windowLedger streamWindow selectedWindow ∧
                  Cont regseqRead realSeal consumerSeal ∧ hsame windowLedger consumerSeal ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle selectedWindow pkg := by
  intro carrier windowSelection consumerSealRow selectedPkg
  obtain ⟨ratSeedUnary, streamWindowUnary, regseqReadUnary, realSealUnary,
    windowLedgerUnary, _provenanceUnary, _localCertUnary, _ratStreamRegseq,
    regseqSealLedger, _sealLocalProvenance, provenancePkg⟩ := carrier
  have selectedWindowUnary : UnaryHistory selectedWindow :=
    unary_cont_closed windowLedgerUnary streamWindowUnary windowSelection
  have consumerSealUnary : UnaryHistory consumerSeal :=
    unary_cont_closed regseqReadUnary realSealUnary consumerSealRow
  have ledgerSameConsumer : hsame windowLedger consumerSeal :=
    cont_deterministic regseqSealLedger consumerSealRow
  exact
    ⟨ratSeedUnary, streamWindowUnary, regseqReadUnary, windowLedgerUnary,
      selectedWindowUnary, consumerSealUnary, windowSelection, consumerSealRow,
      ledgerSameConsumer, provenancePkg, selectedPkg⟩

theorem RegularCauchyDiagonalCarrier_root_selector_totality [AskSetup] [PackageSetup]
    {ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert selectedWindow
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
        provenance localCert bundle pkg ->
      Cont windowLedger streamWindow selectedWindow ->
        Cont regseqRead realSeal sealRead ->
          PkgSig bundle selectedWindow pkg ->
            PkgSig bundle sealRead pkg ->
              UnaryHistory ratSeed ∧ UnaryHistory streamWindow ∧ UnaryHistory regseqRead ∧
                UnaryHistory realSeal ∧ UnaryHistory windowLedger ∧
                  UnaryHistory selectedWindow ∧ UnaryHistory sealRead ∧
                    Cont windowLedger streamWindow selectedWindow ∧
                      Cont regseqRead realSeal sealRead ∧ hsame windowLedger sealRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle selectedWindow pkg ∧
                          PkgSig bundle sealRead pkg := by
  intro carrier windowSelection sealReadRow selectedPkg sealReadPkg
  obtain ⟨ratSeedUnary, streamWindowUnary, regseqReadUnary, realSealUnary,
    windowLedgerUnary, _provenanceUnary, _localCertUnary, _ratStreamRegseq,
    regseqSealLedger, _sealLocalProvenance, provenancePkg⟩ := carrier
  have selectedWindowUnary : UnaryHistory selectedWindow :=
    unary_cont_closed windowLedgerUnary streamWindowUnary windowSelection
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regseqReadUnary realSealUnary sealReadRow
  have ledgerSameSealRead : hsame windowLedger sealRead :=
    cont_deterministic regseqSealLedger sealReadRow
  exact
    ⟨ratSeedUnary, streamWindowUnary, regseqReadUnary, realSealUnary, windowLedgerUnary,
      selectedWindowUnary, sealReadUnary, windowSelection, sealReadRow, ledgerSameSealRead,
      provenancePkg, selectedPkg, sealReadPkg⟩

theorem RegularCauchyDiagonalCarrier_root_seal_route_exhaustion [AskSetup] [PackageSetup]
    {ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert selectedWindow
      sealRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
        provenance localCert bundle pkg ->
      Cont windowLedger streamWindow selectedWindow ->
        Cont regseqRead realSeal sealRead ->
          Cont realSeal provenance endpoint ->
            PkgSig bundle selectedWindow pkg ->
              PkgSig bundle endpoint pkg ->
                UnaryHistory ratSeed ∧ UnaryHistory streamWindow ∧ UnaryHistory regseqRead ∧
                  UnaryHistory realSeal ∧ UnaryHistory windowLedger ∧
                    UnaryHistory selectedWindow ∧ UnaryHistory sealRead ∧
                      UnaryHistory endpoint ∧ Cont windowLedger streamWindow selectedWindow ∧
                        Cont regseqRead realSeal sealRead ∧
                          Cont realSeal provenance endpoint ∧ hsame windowLedger sealRead ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle selectedWindow pkg ∧
                              PkgSig bundle endpoint pkg := by
  intro carrier windowSelection sealReadRow endpointRow selectedPkg endpointPkg
  obtain ⟨ratSeedUnary, streamWindowUnary, regseqReadUnary, realSealUnary,
    windowLedgerUnary, provenanceUnary, _localCertUnary, _ratStreamRegseq,
    regseqSealLedger, _sealLocalProvenance, provenancePkg⟩ := carrier
  have selectedWindowUnary : UnaryHistory selectedWindow :=
    unary_cont_closed windowLedgerUnary streamWindowUnary windowSelection
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regseqReadUnary realSealUnary sealReadRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed realSealUnary provenanceUnary endpointRow
  have ledgerSameSealRead : hsame windowLedger sealRead :=
    cont_deterministic regseqSealLedger sealReadRow
  exact
    ⟨ratSeedUnary, streamWindowUnary, regseqReadUnary, realSealUnary, windowLedgerUnary,
      selectedWindowUnary, sealReadUnary, endpointUnary, windowSelection, sealReadRow,
      endpointRow, ledgerSameSealRead, provenancePkg, selectedPkg, endpointPkg⟩

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

theorem RegularCauchyDiagonalCarrier_bridge_route_determinacy [AskSetup] [PackageSetup]
    {ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert selectedWindow
      completionRead alternateRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
        provenance localCert bundle pkg ->
      Cont windowLedger streamWindow selectedWindow ->
        Cont selectedWindow regseqRead completionRead ->
          Cont selectedWindow regseqRead alternateRead ->
            PkgSig bundle completionRead pkg ->
              PkgSig bundle alternateRead pkg ->
                hsame completionRead alternateRead ∧ UnaryHistory completionRead ∧
                  UnaryHistory alternateRead ∧ PkgSig bundle provenance pkg := by
  intro carrier windowSelection completionRow alternateRow _completionPkg _alternatePkg
  obtain ⟨_ratSeedUnary, streamWindowUnary, regseqReadUnary, _realSealUnary,
    windowLedgerUnary, _provenanceUnary, _localCertUnary, _ratStreamRegseq,
    _regseqSealLedger, _sealLocalProvenance, provenancePkg⟩ := carrier
  have selectedWindowUnary : UnaryHistory selectedWindow :=
    unary_cont_closed windowLedgerUnary streamWindowUnary windowSelection
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed selectedWindowUnary regseqReadUnary completionRow
  have alternateUnary : UnaryHistory alternateRead :=
    unary_cont_closed selectedWindowUnary regseqReadUnary alternateRow
  have completionSameAlternate : hsame completionRead alternateRead :=
    cont_deterministic completionRow alternateRow
  exact ⟨completionSameAlternate, completionUnary, alternateUnary, provenancePkg⟩

theorem RegularCauchyDiagonalCarrier_bridge_non_escape_certificate [AskSetup] [PackageSetup]
    {ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert selectedWindow
      completionRead directCompletion : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
        provenance localCert bundle pkg ->
      Cont windowLedger streamWindow selectedWindow ->
        Cont selectedWindow regseqRead completionRead ->
          Cont windowLedger (append streamWindow regseqRead) directCompletion ->
            PkgSig bundle completionRead pkg ->
              PkgSig bundle directCompletion pkg ->
                hsame completionRead directCompletion ∧ UnaryHistory completionRead ∧
                  UnaryHistory directCompletion ∧ PkgSig bundle provenance pkg := by
  intro carrier windowSelection completionRow directCompletionRow _completionPkg
    _directCompletionPkg
  obtain ⟨_ratSeedUnary, streamWindowUnary, regseqReadUnary, _realSealUnary,
    windowLedgerUnary, _provenanceUnary, _localCertUnary, _ratStreamRegseq,
    _regseqSealLedger, _sealLocalProvenance, provenancePkg⟩ := carrier
  have selectedWindowUnary : UnaryHistory selectedWindow :=
    unary_cont_closed windowLedgerUnary streamWindowUnary windowSelection
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed selectedWindowUnary regseqReadUnary completionRow
  have streamRegseqUnary : UnaryHistory (append streamWindow regseqRead) :=
    unary_cont_closed streamWindowUnary regseqReadUnary (cont_intro rfl)
  have directCompletionUnary : UnaryHistory directCompletion :=
    unary_cont_closed windowLedgerUnary streamRegseqUnary directCompletionRow
  have completionDirectRow :
      Cont windowLedger (append streamWindow regseqRead) completionRead := by
    cases windowSelection
    cases completionRow
    exact append_assoc windowLedger streamWindow regseqRead
  have completionSameDirect : hsame completionRead directCompletion :=
    cont_deterministic completionDirectRow directCompletionRow
  exact ⟨completionSameDirect, completionUnary, directCompletionUnary, provenancePkg⟩

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

theorem RegularCauchyDiagonalCarrier_semantic_name_certificate [AskSetup] [PackageSetup]
    {ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
        provenance localCert bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          hsame row provenance ∧
            RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
              provenance localCert bundle pkg)
        (fun row : BHist => hsame row provenance)
        (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
        hsame := by
  intro carrier
  have carrierProof := carrier
  obtain ⟨_ratSeedUnary, _streamWindowUnary, _regseqReadUnary, _realSealUnary,
    _windowLedgerUnary, _provenanceUnary, _localCertUnary, _ratStreamRegseq,
    _regseqSealLedger, _sealLocalProvenance, pkgSig⟩ := carrier
  have sourceProvenance :
      (fun row : BHist =>
        hsame row provenance ∧
          RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
            provenance localCert bundle pkg) provenance := by
    exact ⟨hsame_refl provenance, carrierProof⟩
  have core :
      NameCert
        (fun row : BHist =>
          hsame row provenance ∧
            RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
              provenance localCert bundle pkg)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro provenance sourceProvenance
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row other same
        exact hsame_symm same
      equiv_trans := by
        intro row other third sameRO sameOT
        exact hsame_trans sameRO sameOT
      carrier_respects_equiv := by
        intro row other same source
        constructor
        · exact hsame_trans (hsame_symm same) source.left
        · exact source.right
    }
  exact {
    core := core
    pattern_sound := by
      intro row source
      exact source.left
    ledger_sound := by
      intro row source
      exact ⟨source.left, pkgSig⟩
  }

theorem RegularCauchyDiagonalCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
        provenance localCert bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row realSeal ∧
              RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal
                windowLedger provenance localCert bundle pkg)
          (fun row : BHist => hsame row realSeal ∧ UnaryHistory windowLedger)
          (fun row : BHist => hsame row realSeal ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory ratSeed ∧ UnaryHistory streamWindow ∧ UnaryHistory regseqRead ∧
          UnaryHistory realSeal ∧ UnaryHistory windowLedger ∧ PkgSig bundle provenance pkg := by
  intro carrier
  have carrierSource := carrier
  obtain ⟨ratSeedUnary, streamWindowUnary, regseqReadUnary, realSealUnary, windowLedgerUnary,
    _provenanceUnary, _localCertUnary, _ratStreamRegseq, _regseqSealLedger,
    _sealLocalProvenance, provenancePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row realSeal ∧
              RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal
                windowLedger provenance localCert bundle pkg)
          (fun row : BHist => hsame row realSeal ∧ UnaryHistory windowLedger)
          (fun row : BHist => hsame row realSeal ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realSeal (And.intro (hsame_refl realSeal) carrierSource)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro row source
      exact And.intro source.left windowLedgerUnary
    ledger_sound := by
      intro row source
      exact And.intro source.left provenancePkg
  }
  exact
    ⟨cert, ratSeedUnary, streamWindowUnary, regseqReadUnary, realSealUnary, windowLedgerUnary,
      provenancePkg⟩

theorem RegularCauchyDiagonalCarrier_selector_fiber_exhaustion [AskSetup] [PackageSetup]
    {ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert selectedWindow
      fiberRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
        provenance localCert bundle pkg ->
      Cont windowLedger streamWindow selectedWindow ->
        Cont selectedWindow regseqRead fiberRead ->
          Cont regseqRead realSeal sealRead ->
            PkgSig bundle fiberRead pkg ->
              PkgSig bundle sealRead pkg ->
                UnaryHistory selectedWindow ∧ UnaryHistory fiberRead ∧
                  UnaryHistory sealRead ∧ Cont windowLedger streamWindow selectedWindow ∧
                    Cont selectedWindow regseqRead fiberRead ∧
                      Cont regseqRead realSeal sealRead ∧ hsame windowLedger sealRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle fiberRead pkg ∧
                          PkgSig bundle sealRead pkg := by
  intro carrier windowSelection fiberRoute sealRoute fiberPkg sealPkg
  obtain ⟨_ratSeedUnary, streamWindowUnary, regseqReadUnary, realSealUnary,
    windowLedgerUnary, _provenanceUnary, _localCertUnary, _ratStreamRegseq,
    regseqSealLedger, _sealLocalProvenance, provenancePkg⟩ := carrier
  have selectedWindowUnary : UnaryHistory selectedWindow :=
    unary_cont_closed windowLedgerUnary streamWindowUnary windowSelection
  have fiberUnary : UnaryHistory fiberRead :=
    unary_cont_closed selectedWindowUnary regseqReadUnary fiberRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regseqReadUnary realSealUnary sealRoute
  have ledgerSameSeal : hsame windowLedger sealRead :=
    cont_deterministic regseqSealLedger sealRoute
  exact
    ⟨selectedWindowUnary, fiberUnary, sealUnary, windowSelection, fiberRoute, sealRoute,
      ledgerSameSeal, provenancePkg, fiberPkg, sealPkg⟩

theorem RegularCauchyDiagonalCarrier_bridge_obligation_package [AskSetup] [PackageSetup]
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
                    UnaryHistory regseqRead ∧ UnaryHistory selectedWindow ∧
                      UnaryHistory sealRead ∧ UnaryHistory completionRead ∧
                        Cont windowLedger streamWindow selectedWindow ∧
                          Cont regseqRead realSeal sealRead ∧
                            Cont selectedWindow regseqRead completionRead ∧
                              hsame windowLedger sealRead ∧ PkgSig bundle provenance pkg ∧
                                PkgSig bundle selectedWindow pkg ∧ PkgSig bundle sealRead pkg ∧
                                  PkgSig bundle completionRead pkg := by
  intro carrier windowSelection sealReadRow completionRow selectedPkg sealReadPkg completionPkg
  obtain ⟨ratSeedUnary, streamWindowUnary, regseqReadUnary, realSealUnary,
    windowLedgerUnary, _provenanceUnary, _localCertUnary, _ratStreamRegseq,
    regseqSealLedger, _sealLocalProvenance, provenancePkg⟩ := carrier
  have selectedWindowUnary : UnaryHistory selectedWindow :=
    unary_cont_closed windowLedgerUnary streamWindowUnary windowSelection
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regseqReadUnary realSealUnary sealReadRow
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed selectedWindowUnary regseqReadUnary completionRow
  have ledgerSameSealRead : hsame windowLedger sealRead :=
    cont_deterministic regseqSealLedger sealReadRow
  exact
    ⟨ratSeedUnary, streamWindowUnary, regseqReadUnary, selectedWindowUnary, sealReadUnary,
      completionReadUnary, windowSelection, sealReadRow, completionRow, ledgerSameSealRead,
      provenancePkg, selectedPkg, sealReadPkg, completionPkg⟩

theorem RegularCauchyDiagonalCarrier_real_completion_handoff [AskSetup] [PackageSetup]
    {ratSeed streamWindow regseqRead realSeal windowLedger provenance localCert selectedWindow
      completionRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyDiagonalCarrier ratSeed streamWindow regseqRead realSeal windowLedger
        provenance localCert bundle pkg ->
      Cont windowLedger streamWindow selectedWindow ->
        Cont selectedWindow regseqRead completionRead ->
          Cont regseqRead realSeal sealRead ->
            PkgSig bundle completionRead pkg ->
              PkgSig bundle sealRead pkg ->
                UnaryHistory selectedWindow ∧ UnaryHistory completionRead ∧
                  UnaryHistory sealRead ∧ Cont selectedWindow regseqRead completionRead ∧
                    Cont regseqRead realSeal sealRead ∧ hsame windowLedger sealRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle completionRead pkg ∧
                        PkgSig bundle sealRead pkg := by
  intro carrier windowSelection completionRow sealReadRow completionPkg sealReadPkg
  obtain ⟨_ratSeedUnary, streamWindowUnary, regseqReadUnary, realSealUnary,
    windowLedgerUnary, _provenanceUnary, _localCertUnary, _ratStreamRegseq,
    regseqSealLedger, _sealLocalProvenance, provenancePkg⟩ := carrier
  have selectedWindowUnary : UnaryHistory selectedWindow :=
    unary_cont_closed windowLedgerUnary streamWindowUnary windowSelection
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed selectedWindowUnary regseqReadUnary completionRow
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regseqReadUnary realSealUnary sealReadRow
  have ledgerSameSealRead : hsame windowLedger sealRead :=
    cont_deterministic regseqSealLedger sealReadRow
  exact
    ⟨selectedWindowUnary, completionUnary, sealReadUnary, completionRow, sealReadRow,
      ledgerSameSealRead, provenancePkg, completionPkg, sealReadPkg⟩

end BEDC.Derived.RegularCauchyDiagonalUp
