import BEDC.Derived.RealSequenceLimitUp.NameCertObligations

namespace BEDC.Derived.RealSequenceLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealSequenceLimitTailRefinementLedger [AskSetup] [PackageSetup]
    {sequenceRow limitRow windowSchedule dyadicLedger classifierRow transport route provenance
      name refinedTolerance refinedThreshold refinedAdmitted : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealSequenceLimitCarrier sequenceRow limitRow windowSchedule dyadicLedger classifierRow
        transport route provenance name bundle pkg ->
      Cont dyadicLedger refinedTolerance refinedThreshold ->
        Cont refinedThreshold classifierRow refinedAdmitted ->
          PkgSig bundle refinedAdmitted pkg ->
            UnaryHistory refinedTolerance ->
              UnaryHistory dyadicLedger ∧ UnaryHistory refinedTolerance ∧
                UnaryHistory refinedThreshold ∧ UnaryHistory refinedAdmitted ∧
                  Cont dyadicLedger refinedTolerance refinedThreshold ∧
                    Cont refinedThreshold classifierRow refinedAdmitted ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle refinedAdmitted pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier thresholdCont admittedCont admittedPkg refinedToleranceUnary
  rcases carrier with
    ⟨_sequenceUnary, _limitUnary, _windowUnary, dyadicUnary, classifierUnary, _transportUnary,
      _routeUnary, _provenanceUnary, _nameUnary, _routeCont, _classifierCont, _transportSame,
      _routeSame, provenancePkg, _namePkg⟩
  have refinedThresholdUnary : UnaryHistory refinedThreshold :=
    unary_cont_closed dyadicUnary refinedToleranceUnary thresholdCont
  have refinedAdmittedUnary : UnaryHistory refinedAdmitted :=
    unary_cont_closed refinedThresholdUnary classifierUnary admittedCont
  exact
    ⟨dyadicUnary, refinedToleranceUnary, refinedThresholdUnary, refinedAdmittedUnary,
      thresholdCont, admittedCont, provenancePkg, admittedPkg⟩

end BEDC.Derived.RealSequenceLimitUp
