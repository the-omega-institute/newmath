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

end BEDC.Derived.RegularCauchyDiagonalUp
