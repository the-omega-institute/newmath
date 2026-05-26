import BEDC.Derived.RealSequenceLimitUp.ClassifierStability

namespace BEDC.Derived.RealSequenceLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealSequenceLimitRegularClassifierTransport [AskSetup] [PackageSetup]
    {sequenceRow limitRow windowSchedule dyadicLedger classifierRow transport route provenance
      name transportedClassifier transportedRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealSequenceLimitCarrier sequenceRow limitRow windowSchedule dyadicLedger classifierRow
        transport route provenance name bundle pkg ->
      hsame classifierRow transportedClassifier ->
        Cont transportedClassifier route transportedRoute ->
          PkgSig bundle transportedRoute pkg ->
            UnaryHistory transportedClassifier ∧ UnaryHistory transportedRoute ∧
              RealSequenceLimitCarrier sequenceRow limitRow windowSchedule dyadicLedger
                transportedClassifier transport route provenance name bundle pkg ∧
                Cont transportedClassifier route transportedRoute ∧
                  PkgSig bundle transportedRoute pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle PkgSig
  intro carrier sameClassifier transportedCont transportedPkg
  have transportedCarrier :=
    RealSequenceLimitClassifierStability carrier sameClassifier
  rcases transportedCarrier with ⟨transportedUnary, carrier'⟩
  have carrierOut := carrier'
  rcases carrier' with
    ⟨_sequenceUnary, _limitUnary, _windowUnary, _dyadicUnary, classifierUnary, _transportUnary,
      routeUnary, _provenanceUnary, _nameUnary, _routeCont, _classifierCont, _transportSame,
      _routeSame, _provenancePkg, _namePkg⟩
  have transportedRouteUnary : UnaryHistory transportedRoute :=
    unary_cont_closed classifierUnary routeUnary transportedCont
  exact ⟨transportedUnary, transportedRouteUnary, carrierOut, transportedCont, transportedPkg⟩

end BEDC.Derived.RealSequenceLimitUp
