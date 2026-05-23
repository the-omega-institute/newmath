import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ArchimedeanRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ArchimedeanRealPacket [AskSetup] [PackageSetup]
    (real bound dyadic stream regseq ledger transport continuation provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory real ∧ UnaryHistory bound ∧ UnaryHistory dyadic ∧ UnaryHistory stream ∧
    UnaryHistory regseq ∧ UnaryHistory ledger ∧ UnaryHistory transport ∧
      UnaryHistory continuation ∧ UnaryHistory provenance ∧ UnaryHistory nameCert ∧
        Cont stream regseq ledger ∧ Cont ledger transport continuation ∧
          Cont continuation provenance real ∧ PkgSig bundle bound pkg ∧
            PkgSig bundle provenance pkg

theorem ArchimedeanRealPacket_rational_bound_witness [AskSetup] [PackageSetup]
    {real bound dyadic stream regseq ledger transport continuation provenance nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArchimedeanRealPacket real bound dyadic stream regseq ledger transport continuation
      provenance nameCert bundle pkg ->
      ∃ boundWitness dyadicWitness : BHist,
        hsame boundWitness bound ∧ hsame dyadicWitness dyadic ∧ UnaryHistory boundWitness ∧
          UnaryHistory dyadicWitness ∧ Cont stream regseq ledger ∧
            PkgSig bundle boundWitness pkg := by
  intro packet
  obtain ⟨_realUnary, boundUnary, dyadicUnary, _streamUnary, _regseqUnary, _ledgerUnary,
    _transportUnary, _continuationUnary, _provenanceUnary, _nameCertUnary, streamRegseqLedger,
    _ledgerTransportContinuation, _continuationProvenanceReal, boundPkg,
    _provenancePkg⟩ := packet
  exact
    ⟨bound, dyadic, hsame_refl bound, hsame_refl dyadic, boundUnary, dyadicUnary,
      streamRegseqLedger, boundPkg⟩

def ArchimedeanRealCarrier [AskSetup] [PackageSetup]
    (realName ratBound dyadicBound streamWindow regseqHandoff boundLedger transport routes
      provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory realName ∧ UnaryHistory ratBound ∧ UnaryHistory dyadicBound ∧
    UnaryHistory streamWindow ∧ UnaryHistory regseqHandoff ∧ UnaryHistory boundLedger ∧
      UnaryHistory transport ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
        UnaryHistory localCert ∧ Cont realName streamWindow regseqHandoff ∧
          Cont ratBound dyadicBound boundLedger ∧ Cont regseqHandoff boundLedger transport ∧
            Cont transport routes provenance ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localCert pkg

theorem ArchimedeanRealCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {realName ratBound dyadicBound streamWindow regseqHandoff boundLedger transport routes
      provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArchimedeanRealCarrier realName ratBound dyadicBound streamWindow regseqHandoff
        boundLedger transport routes provenance localCert bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          hsame row realName ∧
            ArchimedeanRealCarrier realName ratBound dyadicBound streamWindow
              regseqHandoff boundLedger transport routes provenance localCert bundle pkg)
        (fun _row : BHist =>
          UnaryHistory realName ∧ UnaryHistory ratBound ∧ UnaryHistory dyadicBound ∧
            Cont realName streamWindow regseqHandoff ∧ Cont ratBound dyadicBound boundLedger)
        (fun row : BHist => PkgSig bundle provenance pkg ∧ UnaryHistory row)
        hsame := by
  intro carrier
  have carrierWitness := carrier
  obtain ⟨realNameUnary, ratBoundUnary, dyadicBoundUnary, _streamWindowUnary,
    _regseqHandoffUnary, _boundLedgerUnary, _transportUnary, _routesUnary, _provenanceUnary,
    _localCertUnary, realNameStreamWindowRegseq, ratDyadicBoundLedger,
    _regseqLedgerTransport, _transportRoutesProvenance, provenancePkg, _localCertPkg⟩ :=
    carrier
  have sourceRealName :
      (fun row : BHist =>
        hsame row realName ∧
          ArchimedeanRealCarrier realName ratBound dyadicBound streamWindow regseqHandoff
            boundLedger transport routes provenance localCert bundle pkg) realName := by
    exact And.intro (hsame_refl realName) carrierWitness
  have core :
      NameCert
        (fun row : BHist =>
          hsame row realName ∧
            ArchimedeanRealCarrier realName ratBound dyadicBound streamWindow regseqHandoff
              boundLedger transport routes provenance localCert bundle pkg)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro realName sourceRealName
      equiv_refl := by
        intro h _source
        exact hsame_refl h
      equiv_symm := by
        intro h k same
        exact hsame_symm same
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k sameHK sourceH
        have sameHRealName : hsame h realName := sourceH.left
        have sameKRealName : hsame k realName :=
          hsame_trans (hsame_symm sameHK) sameHRealName
        exact And.intro sameKRealName sourceH.right
    }
  exact {
    core := core
    pattern_sound := by
      intro _row _source
      exact
        ⟨realNameUnary, ratBoundUnary, dyadicBoundUnary, realNameStreamWindowRegseq,
          ratDyadicBoundLedger⟩
    ledger_sound := by
      intro row source
      have rowUnary : UnaryHistory row :=
        unary_transport realNameUnary (hsame_symm source.left)
      exact And.intro provenancePkg rowUnary
  }

theorem ArchimedeanRealCarrier_rat_dyadic_bound_coherence [AskSetup] [PackageSetup]
    {realName ratBound dyadicBound streamWindow regseqHandoff boundLedger transport routes
      provenance localCert coherenceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArchimedeanRealCarrier realName ratBound dyadicBound streamWindow regseqHandoff
        boundLedger transport routes provenance localCert bundle pkg ->
      Cont boundLedger provenance coherenceRead ->
        PkgSig bundle coherenceRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                hsame row realName ∧
                  ArchimedeanRealCarrier realName ratBound dyadicBound streamWindow
                    regseqHandoff boundLedger transport routes provenance localCert bundle pkg)
              (fun _row : BHist =>
                UnaryHistory realName ∧ UnaryHistory ratBound ∧ UnaryHistory dyadicBound ∧
                  Cont realName streamWindow regseqHandoff ∧
                    Cont ratBound dyadicBound boundLedger)
              (fun row : BHist => PkgSig bundle provenance pkg ∧ UnaryHistory row)
              hsame ∧
            UnaryHistory ratBound ∧ UnaryHistory dyadicBound ∧ UnaryHistory boundLedger ∧
              UnaryHistory coherenceRead ∧ Cont ratBound dyadicBound boundLedger ∧
                Cont boundLedger provenance coherenceRead ∧
                  PkgSig bundle coherenceRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig SemanticNameCert UnaryHistory
  intro carrier boundProvenanceCoherence coherencePkg
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row realName ∧
            ArchimedeanRealCarrier realName ratBound dyadicBound streamWindow regseqHandoff
              boundLedger transport routes provenance localCert bundle pkg)
        (fun _row : BHist =>
          UnaryHistory realName ∧ UnaryHistory ratBound ∧ UnaryHistory dyadicBound ∧
            Cont realName streamWindow regseqHandoff ∧ Cont ratBound dyadicBound boundLedger)
        (fun row : BHist => PkgSig bundle provenance pkg ∧ UnaryHistory row)
        hsame :=
    ArchimedeanRealCarrier_namecert_obligations carrier
  obtain ⟨_realNameUnary, ratBoundUnary, dyadicBoundUnary, _streamWindowUnary,
    _regseqHandoffUnary, boundLedgerUnary, _transportUnary, _routesUnary, provenanceUnary,
    _localCertUnary, _realNameStreamWindowRegseq, ratDyadicBoundLedger,
    _regseqLedgerTransport, _transportRoutesProvenance, _provenancePkg, _localCertPkg⟩ :=
    carrier
  have coherenceUnary : UnaryHistory coherenceRead :=
    unary_cont_closed boundLedgerUnary provenanceUnary boundProvenanceCoherence
  exact
    ⟨cert, ratBoundUnary, dyadicBoundUnary, boundLedgerUnary, coherenceUnary,
      ratDyadicBoundLedger, boundProvenanceCoherence, coherencePkg⟩

theorem ArchimedeanRealCarrier_transported_bound_stability [AskSetup] [PackageSetup]
    {realName ratBound dyadicBound streamWindow regseqHandoff boundLedger transport routes
      provenance localCert realName' ratBound' dyadicBound' streamWindow' regseqHandoff'
      boundLedger' transport' routes' provenance' localCert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArchimedeanRealCarrier realName ratBound dyadicBound streamWindow regseqHandoff
        boundLedger transport routes provenance localCert bundle pkg ->
      hsame realName realName' ->
        hsame ratBound ratBound' ->
          hsame dyadicBound dyadicBound' ->
            hsame streamWindow streamWindow' ->
              hsame routes routes' ->
                hsame provenance provenance' ->
                  hsame localCert localCert' ->
                    Cont realName' streamWindow' regseqHandoff' ->
                      Cont ratBound' dyadicBound' boundLedger' ->
                        Cont regseqHandoff' boundLedger' transport' ->
                          Cont transport' routes' provenance' ->
                            PkgSig bundle provenance' pkg ->
                              PkgSig bundle localCert' pkg ->
                                ArchimedeanRealCarrier realName' ratBound' dyadicBound'
                                      streamWindow' regseqHandoff' boundLedger' transport'
                                      routes' provenance' localCert' bundle pkg ∧
                                  hsame regseqHandoff regseqHandoff' ∧
                                    hsame boundLedger boundLedger' ∧
                                      hsame transport transport' := by
  intro carrier sameRealName sameRatBound sameDyadicBound sameStreamWindow sameRoutes
    sameProvenance sameLocalCert realNameStreamWindowRegseq' ratDyadicBoundLedger'
    regseqLedgerTransport' transportRoutesProvenance' provenancePkg' localCertPkg'
  obtain ⟨realNameUnary, ratBoundUnary, dyadicBoundUnary, streamWindowUnary,
    _regseqHandoffUnary, _boundLedgerUnary, _transportUnary, routesUnary, provenanceUnary,
    localCertUnary, realNameStreamWindowRegseq, ratDyadicBoundLedger, regseqLedgerTransport,
    transportRoutesProvenance, _provenancePkg, _localCertPkg⟩ := carrier
  have realNameUnary' : UnaryHistory realName' :=
    unary_transport realNameUnary sameRealName
  have ratBoundUnary' : UnaryHistory ratBound' :=
    unary_transport ratBoundUnary sameRatBound
  have dyadicBoundUnary' : UnaryHistory dyadicBound' :=
    unary_transport dyadicBoundUnary sameDyadicBound
  have streamWindowUnary' : UnaryHistory streamWindow' :=
    unary_transport streamWindowUnary sameStreamWindow
  have routesUnary' : UnaryHistory routes' :=
    unary_transport routesUnary sameRoutes
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have localCertUnary' : UnaryHistory localCert' :=
    unary_transport localCertUnary sameLocalCert
  have regseqSame : hsame regseqHandoff regseqHandoff' :=
    cont_respects_hsame sameRealName sameStreamWindow realNameStreamWindowRegseq
      realNameStreamWindowRegseq'
  have boundLedgerSame : hsame boundLedger boundLedger' :=
    cont_respects_hsame sameRatBound sameDyadicBound ratDyadicBoundLedger
      ratDyadicBoundLedger'
  have regseqHandoffUnary' : UnaryHistory regseqHandoff' :=
    unary_cont_closed realNameUnary' streamWindowUnary' realNameStreamWindowRegseq'
  have boundLedgerUnary' : UnaryHistory boundLedger' :=
    unary_cont_closed ratBoundUnary' dyadicBoundUnary' ratDyadicBoundLedger'
  have transportSame : hsame transport transport' :=
    cont_respects_hsame regseqSame boundLedgerSame regseqLedgerTransport
      regseqLedgerTransport'
  have transportUnary' : UnaryHistory transport' :=
    unary_cont_closed regseqHandoffUnary' boundLedgerUnary' regseqLedgerTransport'
  exact
    ⟨⟨realNameUnary', ratBoundUnary', dyadicBoundUnary', streamWindowUnary',
      regseqHandoffUnary', boundLedgerUnary', transportUnary', routesUnary',
      provenanceUnary', localCertUnary', realNameStreamWindowRegseq', ratDyadicBoundLedger',
      regseqLedgerTransport', transportRoutesProvenance', provenancePkg', localCertPkg'⟩,
      regseqSame, boundLedgerSame, transportSame⟩

theorem ArchimedeanRealCarrier_bound_ledger_nonescape [AskSetup] [PackageSetup]
    {realName ratBound dyadicBound streamWindow regseqHandoff boundLedger transport routes
      provenance localCert zRatBound zDyadicBound zBoundLedger zProvenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArchimedeanRealCarrier realName ratBound dyadicBound streamWindow regseqHandoff
        boundLedger transport routes provenance localCert bundle pkg ->
      (hsame ratBound (BHist.e0 zRatBound) -> False) ∧
        (hsame dyadicBound (BHist.e0 zDyadicBound) -> False) ∧
          (hsame boundLedger (BHist.e0 zBoundLedger) -> False) ∧
            (hsame provenance (BHist.e0 zProvenance) -> False) := by
  intro carrier
  obtain ⟨_realNameUnary, ratBoundUnary, dyadicBoundUnary, _streamWindowUnary,
    _regseqHandoffUnary, boundLedgerUnary, _transportUnary, _routesUnary, provenanceUnary,
    _localCertUnary, _realNameStreamWindowRegseq, _ratDyadicBoundLedger,
    _regseqLedgerTransport, _transportRoutesProvenance, _provenancePkg, _localCertPkg⟩ :=
    carrier
  exact
    ⟨fun sameRatBound =>
        unary_no_zero_extension (unary_transport ratBoundUnary sameRatBound),
      fun sameDyadicBound =>
        unary_no_zero_extension (unary_transport dyadicBoundUnary sameDyadicBound),
      fun sameBoundLedger =>
        unary_no_zero_extension (unary_transport boundLedgerUnary sameBoundLedger),
      fun sameProvenance =>
        unary_no_zero_extension (unary_transport provenanceUnary sameProvenance)⟩

theorem ArchimedeanRealCarrier_scope_closure [AskSetup] [PackageSetup]
    {realName ratBound dyadicBound streamWindow regseqHandoff boundLedger transport routes
      provenance localCert exportRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArchimedeanRealCarrier realName ratBound dyadicBound streamWindow regseqHandoff
        boundLedger transport routes provenance localCert bundle pkg ->
      Cont provenance localCert exportRow ->
        PkgSig bundle exportRow pkg ->
          UnaryHistory realName ∧ UnaryHistory ratBound ∧ UnaryHistory dyadicBound ∧
            UnaryHistory streamWindow ∧ UnaryHistory regseqHandoff ∧
              UnaryHistory boundLedger ∧ UnaryHistory transport ∧ UnaryHistory routes ∧
                UnaryHistory provenance ∧ UnaryHistory localCert ∧ UnaryHistory exportRow ∧
                  Cont realName streamWindow regseqHandoff ∧
                    Cont ratBound dyadicBound boundLedger ∧
                      Cont regseqHandoff boundLedger transport ∧
                        Cont transport routes provenance ∧
                          Cont provenance localCert exportRow ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle localCert pkg ∧
                              PkgSig bundle exportRow pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig
  intro carrier provenanceLocalExport exportPkg
  obtain ⟨realNameUnary, ratBoundUnary, dyadicBoundUnary, streamWindowUnary,
    regseqHandoffUnary, boundLedgerUnary, transportUnary, routesUnary, provenanceUnary,
    localCertUnary, realNameStreamWindowRegseq, ratDyadicBoundLedger, regseqLedgerTransport,
    transportRoutesProvenance, provenancePkg, localCertPkg⟩ := carrier
  have exportUnary : UnaryHistory exportRow :=
    unary_cont_closed provenanceUnary localCertUnary provenanceLocalExport
  exact
    ⟨realNameUnary, ratBoundUnary, dyadicBoundUnary, streamWindowUnary, regseqHandoffUnary,
      boundLedgerUnary, transportUnary, routesUnary, provenanceUnary, localCertUnary,
      exportUnary, realNameStreamWindowRegseq, ratDyadicBoundLedger, regseqLedgerTransport,
      transportRoutesProvenance, provenanceLocalExport, provenancePkg, localCertPkg,
      exportPkg⟩

theorem ArchimedeanRealCarrier_public_bound_export [AskSetup] [PackageSetup]
    {realName ratBound dyadicBound streamWindow regseqHandoff boundLedger transport routes
      provenance localCert exportRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArchimedeanRealCarrier realName ratBound dyadicBound streamWindow regseqHandoff
        boundLedger transport routes provenance localCert bundle pkg ->
      Cont provenance localCert exportRow ->
        PkgSig bundle exportRow pkg ->
          SemanticNameCert
              (fun row : BHist =>
                hsame row realName ∧
                  ArchimedeanRealCarrier realName ratBound dyadicBound streamWindow
                    regseqHandoff boundLedger transport routes provenance localCert bundle pkg)
              (fun _row : BHist =>
                UnaryHistory realName ∧ UnaryHistory ratBound ∧ UnaryHistory dyadicBound ∧
                  Cont realName streamWindow regseqHandoff ∧
                    Cont ratBound dyadicBound boundLedger)
              (fun row : BHist => PkgSig bundle provenance pkg ∧ UnaryHistory row)
              hsame ∧
            UnaryHistory exportRow ∧ Cont provenance localCert exportRow ∧
              PkgSig bundle exportRow pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig SemanticNameCert
  intro carrier provenanceLocalExport exportPkg
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row realName ∧
            ArchimedeanRealCarrier realName ratBound dyadicBound streamWindow regseqHandoff
              boundLedger transport routes provenance localCert bundle pkg)
        (fun _row : BHist =>
          UnaryHistory realName ∧ UnaryHistory ratBound ∧ UnaryHistory dyadicBound ∧
            Cont realName streamWindow regseqHandoff ∧ Cont ratBound dyadicBound boundLedger)
        (fun row : BHist => PkgSig bundle provenance pkg ∧ UnaryHistory row)
        hsame :=
    ArchimedeanRealCarrier_namecert_obligations carrier
  obtain ⟨_realNameUnary, _ratBoundUnary, _dyadicBoundUnary, _streamWindowUnary,
    _regseqHandoffUnary, _boundLedgerUnary, _transportUnary, _routesUnary, provenanceUnary,
    localCertUnary, _realNameStreamWindowRegseq, _ratDyadicBoundLedger,
    _regseqLedgerTransport, _transportRoutesProvenance, _provenancePkg, _localCertPkg⟩ :=
    carrier
  have exportUnary : UnaryHistory exportRow :=
    unary_cont_closed provenanceUnary localCertUnary provenanceLocalExport
  exact ⟨cert, exportUnary, provenanceLocalExport, exportPkg⟩

theorem ArchimedeanRealCarrier_budgeted_observation_handoff [AskSetup] [PackageSetup]
    {realName ratBound dyadicBound streamWindow regseqHandoff boundLedger transport routes
      provenance localCert budgetWindow budgetDyadic budgetSeal exportRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArchimedeanRealCarrier realName ratBound dyadicBound streamWindow regseqHandoff
        boundLedger transport routes provenance localCert bundle pkg ->
      Cont streamWindow dyadicBound budgetWindow ->
        Cont budgetWindow regseqHandoff budgetDyadic ->
          Cont budgetDyadic realName budgetSeal ->
            Cont provenance localCert exportRow ->
              PkgSig bundle budgetSeal pkg ->
                PkgSig bundle exportRow pkg ->
                  UnaryHistory budgetWindow ∧ UnaryHistory budgetDyadic ∧
                    UnaryHistory budgetSeal ∧ UnaryHistory exportRow ∧
                      Cont streamWindow dyadicBound budgetWindow ∧
                        Cont budgetWindow regseqHandoff budgetDyadic ∧
                          Cont budgetDyadic realName budgetSeal ∧
                            Cont provenance localCert exportRow ∧
                              PkgSig bundle budgetSeal pkg ∧
                                PkgSig bundle exportRow pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  intro carrier streamDyadicBudget budgetRegseqDyadic budgetDyadicRealSeal
    provenanceLocalExport budgetSealPkg exportPkg
  obtain ⟨realNameUnary, _ratBoundUnary, dyadicBoundUnary, streamWindowUnary,
    regseqHandoffUnary, _boundLedgerUnary, _transportUnary, _routesUnary, provenanceUnary,
    localCertUnary, _realNameStreamWindowRegseq, _ratDyadicBoundLedger,
    _regseqLedgerTransport, _transportRoutesProvenance, _provenancePkg, _localCertPkg⟩ :=
    carrier
  have budgetWindowUnary : UnaryHistory budgetWindow :=
    unary_cont_closed streamWindowUnary dyadicBoundUnary streamDyadicBudget
  have budgetDyadicUnary : UnaryHistory budgetDyadic :=
    unary_cont_closed budgetWindowUnary regseqHandoffUnary budgetRegseqDyadic
  have budgetSealUnary : UnaryHistory budgetSeal :=
    unary_cont_closed budgetDyadicUnary realNameUnary budgetDyadicRealSeal
  have exportUnary : UnaryHistory exportRow :=
    unary_cont_closed provenanceUnary localCertUnary provenanceLocalExport
  exact
    ⟨budgetWindowUnary, budgetDyadicUnary, budgetSealUnary, exportUnary, streamDyadicBudget,
      budgetRegseqDyadic, budgetDyadicRealSeal, provenanceLocalExport, budgetSealPkg,
      exportPkg⟩

theorem ArchimedeanRealCarrier_consumer_bound_handoff [AskSetup] [PackageSetup]
    {realName ratBound dyadicBound streamWindow regseqHandoff boundLedger transport routes
      provenance localCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArchimedeanRealCarrier realName ratBound dyadicBound streamWindow regseqHandoff
        boundLedger transport routes provenance localCert bundle pkg ->
      Cont boundLedger routes consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory ratBound ∧ UnaryHistory dyadicBound ∧ UnaryHistory streamWindow ∧
            UnaryHistory regseqHandoff ∧ UnaryHistory boundLedger ∧ UnaryHistory consumer ∧
              Cont realName streamWindow regseqHandoff ∧
                Cont ratBound dyadicBound boundLedger ∧ Cont boundLedger routes consumer ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  intro carrier boundRoutesConsumer consumerPkg
  obtain ⟨_realNameUnary, ratBoundUnary, dyadicBoundUnary, streamWindowUnary,
    regseqHandoffUnary, boundLedgerUnary, _transportUnary, routesUnary, _provenanceUnary,
    _localCertUnary, realNameStreamWindowRegseq, ratDyadicBoundLedger,
    _regseqLedgerTransport, _transportRoutesProvenance, provenancePkg, _localCertPkg⟩ :=
    carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed boundLedgerUnary routesUnary boundRoutesConsumer
  exact
    ⟨ratBoundUnary, dyadicBoundUnary, streamWindowUnary, regseqHandoffUnary,
      boundLedgerUnary, consumerUnary, realNameStreamWindowRegseq, ratDyadicBoundLedger,
      boundRoutesConsumer, provenancePkg, consumerPkg⟩

theorem ArchimedeanRealCarrier_dyadic_threshold_totality [AskSetup] [PackageSetup]
    {realName ratBound dyadicBound streamWindow regseqHandoff boundLedger transport routes
      provenance localCert budgetRequest threshold : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArchimedeanRealCarrier realName ratBound dyadicBound streamWindow regseqHandoff
        boundLedger transport routes provenance localCert bundle pkg ->
      UnaryHistory budgetRequest ->
        Cont boundLedger budgetRequest threshold ->
          PkgSig bundle threshold pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  hsame row realName ∧
                    ArchimedeanRealCarrier realName ratBound dyadicBound streamWindow
                      regseqHandoff boundLedger transport routes provenance localCert bundle pkg)
                (fun _row : BHist =>
                  UnaryHistory realName ∧ UnaryHistory ratBound ∧ UnaryHistory dyadicBound ∧
                    Cont realName streamWindow regseqHandoff ∧
                      Cont ratBound dyadicBound boundLedger)
                (fun row : BHist => PkgSig bundle provenance pkg ∧ UnaryHistory row)
                hsame ∧
              UnaryHistory threshold ∧ hsame threshold (append boundLedger budgetRequest) ∧
                PkgSig bundle threshold pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont SemanticNameCert UnaryHistory
  intro carrier budgetRequestUnary boundBudgetThreshold thresholdPkg
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row realName ∧
            ArchimedeanRealCarrier realName ratBound dyadicBound streamWindow regseqHandoff
              boundLedger transport routes provenance localCert bundle pkg)
        (fun _row : BHist =>
          UnaryHistory realName ∧ UnaryHistory ratBound ∧ UnaryHistory dyadicBound ∧
            Cont realName streamWindow regseqHandoff ∧ Cont ratBound dyadicBound boundLedger)
        (fun row : BHist => PkgSig bundle provenance pkg ∧ UnaryHistory row)
        hsame :=
    ArchimedeanRealCarrier_namecert_obligations carrier
  obtain ⟨_realNameUnary, _ratBoundUnary, _dyadicBoundUnary, _streamWindowUnary,
    _regseqHandoffUnary, boundLedgerUnary, _transportUnary, _routesUnary, _provenanceUnary,
    _localCertUnary, _realNameStreamWindowRegseq, _ratDyadicBoundLedger,
    _regseqLedgerTransport, _transportRoutesProvenance, _provenancePkg, _localCertPkg⟩ :=
    carrier
  have thresholdUnary : UnaryHistory threshold :=
    unary_cont_closed boundLedgerUnary budgetRequestUnary boundBudgetThreshold
  exact ⟨cert, thresholdUnary, boundBudgetThreshold, thresholdPkg⟩

theorem ArchimedeanRealCarrier_budgeted_bound_window_exhaustion [AskSetup] [PackageSetup]
    {realName ratBound dyadicBound streamWindow regseqHandoff boundLedger transport routes
      provenance localCert budget threshold : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArchimedeanRealCarrier realName ratBound dyadicBound streamWindow regseqHandoff
        boundLedger transport routes provenance localCert bundle pkg →
      Cont streamWindow dyadicBound budget →
        Cont budget ratBound threshold →
          PkgSig bundle threshold pkg →
            UnaryHistory streamWindow ∧ UnaryHistory dyadicBound ∧ UnaryHistory budget ∧
              UnaryHistory threshold ∧ hsame ratBound ratBound ∧
                Cont streamWindow dyadicBound budget ∧ Cont budget ratBound threshold ∧
                  PkgSig bundle threshold pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier streamDyadicBudget budgetRatThreshold thresholdPkg
  obtain ⟨_realNameUnary, ratBoundUnary, dyadicBoundUnary, streamWindowUnary,
    _regseqHandoffUnary, _boundLedgerUnary, _transportUnary, _routesUnary, _provenanceUnary,
    _localCertUnary, _realNameStreamWindowRegseq, _ratDyadicBoundLedger,
    _regseqLedgerTransport, _transportRoutesProvenance, _provenancePkg, _localCertPkg⟩ :=
    carrier
  have budgetUnary : UnaryHistory budget :=
    unary_cont_closed streamWindowUnary dyadicBoundUnary streamDyadicBudget
  have thresholdUnary : UnaryHistory threshold :=
    unary_cont_closed budgetUnary ratBoundUnary budgetRatThreshold
  exact
    ⟨streamWindowUnary, dyadicBoundUnary, budgetUnary, thresholdUnary,
      hsame_refl ratBound, streamDyadicBudget, budgetRatThreshold, thresholdPkg⟩

end BEDC.Derived.ArchimedeanRealUp
