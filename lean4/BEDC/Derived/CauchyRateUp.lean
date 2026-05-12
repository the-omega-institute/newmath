import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyRateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

end BEDC.Derived.CauchyRateUp
