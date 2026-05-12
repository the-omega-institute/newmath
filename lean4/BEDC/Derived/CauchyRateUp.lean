import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyRateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyRateCarrier [AskSetup] [PackageSetup]
    (precision schedule tolerance family regseq completion transport route provenance
      nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory schedule ∧ UnaryHistory tolerance ∧
    UnaryHistory family ∧ UnaryHistory regseq ∧ UnaryHistory completion ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory nameCert ∧ Cont precision schedule tolerance ∧
          Cont family tolerance regseq ∧ Cont regseq completion transport ∧
            Cont transport route provenance ∧ Cont provenance nameCert completion ∧
              hsame regseq (append family tolerance) ∧ PkgSig bundle provenance pkg

theorem CauchyRateCarrier_regular_family_handoff [AskSetup] [PackageSetup]
    {precision schedule tolerance family regseq completion transport route provenance nameCert
      handoffRead rateRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyRateCarrier precision schedule tolerance family regseq completion transport route
        provenance nameCert bundle pkg ->
      Cont family tolerance handoffRead ->
        Cont schedule handoffRead rateRead ->
          UnaryHistory handoffRead ∧ UnaryHistory rateRead ∧
            hsame regseq (append family tolerance) ∧ PkgSig bundle provenance pkg := by
  intro carrier handoffReadRow rateReadRow
  obtain ⟨_precisionUnary, scheduleUnary, toleranceUnary, familyUnary, _regseqUnary,
    _completionUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary,
    _precisionScheduleTolerance, _familyToleranceRegseq, _regseqCompletionTransport,
    _transportRouteProvenance, _provenanceNameCertCompletion, regseqSame, pkgSig⟩ := carrier
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed familyUnary toleranceUnary handoffReadRow
  have rateReadUnary : UnaryHistory rateRead :=
    unary_cont_closed scheduleUnary handoffReadUnary rateReadRow
  exact ⟨handoffReadUnary, rateReadUnary, regseqSame, pkgSig⟩

theorem CauchyRateCarrier_real_cauchy_consumer_boundary [AskSetup] [PackageSetup]
    {precision schedule tolerance family regseq completion transport route provenance
      nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyRateCarrier precision schedule tolerance family regseq completion transport route
        provenance nameCert bundle pkg ->
      UnaryHistory completion ∧ hsame regseq (append family tolerance) ∧
        hsame completion (append provenance nameCert) ∧ Cont regseq completion transport ∧
          PkgSig bundle provenance pkg := by
  intro carrier
  obtain ⟨_precisionUnary, _scheduleUnary, _toleranceUnary, _familyUnary, _regseqUnary,
    completionUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary,
    _precisionScheduleTolerance, _familyToleranceRegseq, regseqCompletionTransport,
    _transportRouteProvenance, provenanceNameCertCompletion, regseqSame, pkgSig⟩ := carrier
  exact And.intro completionUnary
    (And.intro regseqSame
      (And.intro provenanceNameCertCompletion
        (And.intro regseqCompletionTransport pkgSig)))

theorem CauchyRateCarrier_real_completion_consumer_boundary [AskSetup] [PackageSetup]
    {precision schedule tolerance family regseq completion transport route provenance nameCert
      completionRead completionRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyRateCarrier precision schedule tolerance family regseq completion transport route
        provenance nameCert bundle pkg ->
      Cont regseq completion completionRead ->
        Cont completionRead route completionRoute ->
          UnaryHistory completionRead ∧ UnaryHistory completionRoute ∧
            hsame regseq (append family tolerance) ∧ PkgSig bundle provenance pkg := by
  intro carrier completionReadRow completionRouteRow
  obtain ⟨_precisionUnary, _scheduleUnary, _toleranceUnary, _familyUnary, regseqUnary,
    completionUnary, _transportUnary, routeUnary, _provenanceUnary, _nameCertUnary,
    _precisionScheduleTolerance, _familyToleranceRegseq, _regseqCompletionTransport,
    _transportRouteProvenance, _provenanceNameCertCompletion, regseqSame, pkgSig⟩ := carrier
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed regseqUnary completionUnary completionReadRow
  have completionRouteUnary : UnaryHistory completionRoute :=
    unary_cont_closed completionReadUnary routeUnary completionRouteRow
  exact ⟨completionReadUnary, completionRouteUnary, regseqSame, pkgSig⟩

theorem CauchyRateCarrier_transport_stability [AskSetup] [PackageSetup]
    {precision schedule tolerance family regseq completion transport route provenance nameCert
      precision' schedule' tolerance' family' regseq' completion' transport' route'
        provenance' nameCert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyRateCarrier precision schedule tolerance family regseq completion transport route
        provenance nameCert bundle pkg ->
      hsame precision precision' ->
        hsame schedule schedule' ->
          hsame family family' ->
            hsame completion completion' ->
              hsame route route' ->
                hsame nameCert nameCert' ->
                  Cont precision' schedule' tolerance' ->
                    Cont family' tolerance' regseq' ->
                      Cont regseq' completion' transport' ->
                        Cont transport' route' provenance' ->
                          Cont provenance' nameCert' completion' ->
                            PkgSig bundle provenance' pkg ->
                              CauchyRateCarrier precision' schedule' tolerance' family' regseq'
                                  completion' transport' route' provenance' nameCert'
                                  bundle pkg ∧
                                hsame tolerance tolerance' ∧ hsame regseq regseq' ∧
                                  hsame transport transport' ∧ hsame provenance provenance' := by
  intro carrier precisionSame scheduleSame familySame completionSame routeSame nameCertSame
    precisionScheduleRow familyToleranceRow regseqCompletionRow transportRouteRow
    provenanceNameCertRow provenancePkg
  obtain ⟨precisionUnary, scheduleUnary, toleranceUnary, familyUnary, regseqUnary,
    completionUnary, transportUnary, routeUnary, provenanceUnary, nameCertUnary,
    precisionScheduleTolerance, familyToleranceRegseq, regseqCompletionTransport,
    transportRouteProvenance, provenanceNameCertCompletion, regseqSameAppend,
    _carrierPkg⟩ := carrier
  have precisionUnary' : UnaryHistory precision' :=
    unary_transport precisionUnary precisionSame
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport scheduleUnary scheduleSame
  have toleranceUnary' : UnaryHistory tolerance' :=
    unary_cont_closed precisionUnary' scheduleUnary' precisionScheduleRow
  have familyUnary' : UnaryHistory family' :=
    unary_transport familyUnary familySame
  have regseqUnary' : UnaryHistory regseq' :=
    unary_cont_closed familyUnary' toleranceUnary' familyToleranceRow
  have completionUnary' : UnaryHistory completion' :=
    unary_transport completionUnary completionSame
  have transportUnary' : UnaryHistory transport' :=
    unary_cont_closed regseqUnary' completionUnary' regseqCompletionRow
  have routeUnary' : UnaryHistory route' :=
    unary_transport routeUnary routeSame
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed transportUnary' routeUnary' transportRouteRow
  have nameCertUnary' : UnaryHistory nameCert' :=
    unary_transport nameCertUnary nameCertSame
  have toleranceSame : hsame tolerance tolerance' :=
    cont_respects_hsame precisionSame scheduleSame precisionScheduleTolerance
      precisionScheduleRow
  have regseqSame : hsame regseq regseq' :=
    cont_respects_hsame familySame toleranceSame familyToleranceRegseq familyToleranceRow
  have transportSame : hsame transport transport' :=
    cont_respects_hsame regseqSame completionSame regseqCompletionTransport
      regseqCompletionRow
  have provenanceSame : hsame provenance provenance' :=
    cont_respects_hsame transportSame routeSame transportRouteProvenance transportRouteRow
  have rebuilt :
      CauchyRateCarrier precision' schedule' tolerance' family' regseq' completion'
          transport' route' provenance' nameCert' bundle pkg :=
    ⟨precisionUnary', scheduleUnary', toleranceUnary', familyUnary', regseqUnary',
      completionUnary', transportUnary', routeUnary', provenanceUnary', nameCertUnary',
      precisionScheduleRow, familyToleranceRow, regseqCompletionRow, transportRouteRow,
      provenanceNameCertRow, familyToleranceRow, provenancePkg⟩
  exact
    ⟨rebuilt, toleranceSame, regseqSame, transportSame, provenanceSame⟩

theorem CauchyRateCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {precision schedule tolerance family regseq completion transport route provenance
      nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyRateCarrier precision schedule tolerance family regseq completion transport route
        provenance nameCert bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row completion ∧
              CauchyRateCarrier precision schedule tolerance family regseq completion transport
                route provenance nameCert bundle pkg)
          (fun row : BHist => hsame row completion ∧ Cont regseq completion transport)
          (fun row : BHist => hsame row completion ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory precision ∧ UnaryHistory schedule ∧ UnaryHistory tolerance ∧
          UnaryHistory family ∧ UnaryHistory regseq ∧ UnaryHistory completion ∧
            hsame regseq (append family tolerance) ∧ PkgSig bundle provenance pkg := by
  intro carrier
  have carrierData := carrier
  obtain ⟨precisionUnary, scheduleUnary, toleranceUnary, familyUnary, regseqUnary,
    completionUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary,
    _precisionScheduleTolerance, _familyToleranceRegseq, regseqCompletionTransport,
    _transportRouteProvenance, _provenanceNameCertCompletion, regseqSame, pkgSig⟩ := carrier
  have semanticCert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row completion ∧
              CauchyRateCarrier precision schedule tolerance family regseq completion transport
                route provenance nameCert bundle pkg)
          (fun row : BHist => hsame row completion ∧ Cont regseq completion transport)
          (fun row : BHist => hsame row completion ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completion (And.intro (hsame_refl completion) carrierData)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        exact And.intro (hsame_trans (hsame_symm sameRows) sourceRow.left) sourceRow.right
    }
    pattern_sound := by
      intro _row sourceRow
      exact And.intro sourceRow.left regseqCompletionTransport
    ledger_sound := by
      intro _row sourceRow
      exact And.intro sourceRow.left pkgSig
  }
  exact And.intro semanticCert
    (And.intro precisionUnary
      (And.intro scheduleUnary
        (And.intro toleranceUnary
          (And.intro familyUnary
            (And.intro regseqUnary
              (And.intro completionUnary (And.intro regseqSame pkgSig)))))))

theorem CauchyRateCarrier_ledger_exactness [AskSetup] [PackageSetup]
    {precision schedule tolerance family regseq completion transport route provenance nameCert
      acceptedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyRateCarrier precision schedule tolerance family regseq completion transport route
        provenance nameCert bundle pkg ->
      Cont provenance nameCert acceptedRead ->
        PkgSig bundle acceptedRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                hsame row provenance ∧
                  CauchyRateCarrier precision schedule tolerance family regseq completion
                    transport route provenance nameCert bundle pkg)
              (fun row : BHist => hsame row provenance ∧ UnaryHistory completion)
              (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory precision ∧ UnaryHistory tolerance ∧ UnaryHistory regseq ∧
              UnaryHistory completion ∧ UnaryHistory acceptedRead ∧
                Cont provenance nameCert acceptedRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle acceptedRead pkg := by
  intro carrier acceptedReadRow acceptedPkg
  have carrierSource := carrier
  obtain ⟨precisionUnary, _scheduleUnary, toleranceUnary, _familyUnary, regseqUnary,
    completionUnary, _transportUnary, _routeUnary, provenanceUnary, nameCertUnary,
    _precisionScheduleTolerance, _familyToleranceRegseq, _regseqCompletionTransport,
    _transportRouteProvenance, _provenanceNameCertCompletion, _regseqSame, provenancePkg⟩ :=
    carrier
  have acceptedReadUnary : UnaryHistory acceptedRead :=
    unary_cont_closed provenanceUnary nameCertUnary acceptedReadRow
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row provenance ∧
              CauchyRateCarrier precision schedule tolerance family regseq completion
                transport route provenance nameCert bundle pkg)
          (fun row : BHist => hsame row provenance ∧ UnaryHistory completion)
          (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro provenance
        (And.intro (hsame_refl provenance) carrierSource)
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro row source
      exact And.intro source.left completionUnary
    ledger_sound := by
      intro row source
      exact And.intro source.left provenancePkg
  }
  exact
    ⟨cert, precisionUnary, toleranceUnary, regseqUnary, completionUnary,
      acceptedReadUnary, acceptedReadRow, provenancePkg, acceptedPkg⟩

theorem CauchyRateCarrier_tail_bound_routing [AskSetup] [PackageSetup]
    {precision schedule tolerance family regseq completion transport route provenance
      nameCert tailConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyRateCarrier precision schedule tolerance family regseq completion transport route
        provenance nameCert bundle pkg ->
      Cont tolerance family tailConsumer ->
        UnaryHistory schedule ∧ UnaryHistory tolerance ∧ UnaryHistory family ∧
          UnaryHistory regseq ∧ UnaryHistory tailConsumer ∧ Cont family tolerance regseq ∧
            Cont tolerance family tailConsumer ∧ hsame regseq (append family tolerance) ∧
              PkgSig bundle provenance pkg := by
  intro carrier tailRoute
  obtain ⟨_precisionUnary, scheduleUnary, toleranceUnary, familyUnary, regseqUnary,
    _completionUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary,
    _precisionScheduleTolerance, familyToleranceRegseq, _regseqCompletionTransport,
    _transportRouteProvenance, _provenanceNameCertCompletion, regseqSame, pkgSig⟩ := carrier
  have tailConsumerUnary : UnaryHistory tailConsumer :=
    unary_cont_closed toleranceUnary familyUnary tailRoute
  exact
    ⟨scheduleUnary, toleranceUnary, familyUnary, regseqUnary, tailConsumerUnary,
      familyToleranceRegseq, tailRoute, regseqSame, pkgSig⟩

theorem CauchyRateCarrier_public_certificate [AskSetup] [PackageSetup]
    {precision schedule tolerance family regseq completion transport route provenance nameCert
      acceptedRead completionRead completionRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyRateCarrier precision schedule tolerance family regseq completion transport route
        provenance nameCert bundle pkg ->
      Cont provenance nameCert acceptedRead ->
        Cont regseq completion completionRead ->
          Cont completionRead route completionRoute ->
            PkgSig bundle acceptedRead pkg ->
              PkgSig bundle completionRoute pkg ->
                SemanticNameCert
                  (fun row : BHist => hsame row acceptedRead ∧ UnaryHistory row ∧
                    PkgSig bundle row pkg)
                  (fun row : BHist => hsame row acceptedRead ∧ Cont provenance nameCert row)
                  (fun _row : BHist =>
                    hsame regseq (append family tolerance) ∧ PkgSig bundle provenance pkg)
                  hsame ∧ UnaryHistory completionRead ∧ UnaryHistory completionRoute ∧
                    PkgSig bundle completionRoute pkg := by
  intro carrier acceptedReadRow completionReadRow completionRouteRow acceptedPkg
    completionRoutePkg
  obtain ⟨_precisionUnary, _scheduleUnary, _toleranceUnary, _familyUnary, regseqUnary,
    completionUnary, _transportUnary, routeUnary, provenanceUnary, nameCertUnary,
    _precisionScheduleTolerance, _familyToleranceRegseq, _regseqCompletionTransport,
    _transportRouteProvenance, _provenanceNameCertCompletion, regseqSame,
    provenancePkg⟩ := carrier
  have acceptedReadUnary : UnaryHistory acceptedRead :=
    unary_cont_closed provenanceUnary nameCertUnary acceptedReadRow
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed regseqUnary completionUnary completionReadRow
  have completionRouteUnary : UnaryHistory completionRoute :=
    unary_cont_closed completionReadUnary routeUnary completionRouteRow
  have sourceAccepted :
      hsame acceptedRead acceptedRead ∧ UnaryHistory acceptedRead ∧
        PkgSig bundle acceptedRead pkg :=
    ⟨hsame_refl acceptedRead, acceptedReadUnary, acceptedPkg⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row acceptedRead ∧ UnaryHistory row ∧
          PkgSig bundle row pkg)
        (fun row : BHist => hsame row acceptedRead ∧ Cont provenance nameCert row)
        (fun _row : BHist =>
          hsame regseq (append family tolerance) ∧ PkgSig bundle provenance pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro acceptedRead sourceAccepted
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      cases sourceRow.left
      exact ⟨hsame_refl acceptedRead, acceptedReadRow⟩
    ledger_sound := by
      intro _row _sourceRow
      exact ⟨regseqSame, provenancePkg⟩
  }
  exact ⟨cert, completionReadUnary, completionRouteUnary, completionRoutePkg⟩

end BEDC.Derived.CauchyRateUp
