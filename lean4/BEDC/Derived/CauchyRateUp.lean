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

end BEDC.Derived.CauchyRateUp
