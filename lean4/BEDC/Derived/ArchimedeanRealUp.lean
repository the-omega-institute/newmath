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

end BEDC.Derived.ArchimedeanRealUp
