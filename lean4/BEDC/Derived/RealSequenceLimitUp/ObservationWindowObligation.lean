import BEDC.Derived.RealSequenceLimitUp.NameCertObligations

namespace BEDC.Derived.RealSequenceLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealSequenceLimitObservationWindowObligation [AskSetup] [PackageSetup]
    {sequenceRow limitRow windowSchedule dyadicLedger classifierRow transport route provenance
      name observation admitted : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealSequenceLimitCarrier sequenceRow limitRow windowSchedule dyadicLedger classifierRow
        transport route provenance name bundle pkg ->
      Cont sequenceRow windowSchedule observation ->
        Cont observation dyadicLedger admitted ->
          PkgSig bundle admitted pkg ->
            UnaryHistory sequenceRow ∧ UnaryHistory windowSchedule ∧
              UnaryHistory dyadicLedger ∧ UnaryHistory observation ∧
                UnaryHistory admitted ∧ Cont sequenceRow windowSchedule observation ∧
                  Cont observation dyadicLedger admitted ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle admitted pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier observationCont admittedCont admittedPkg
  rcases carrier with
    ⟨sequenceUnary, _limitUnary, windowUnary, dyadicUnary, _classifierUnary,
      _transportUnary, _routeUnary, _provenanceUnary, _nameUnary, _routeCont,
      _classifierCont, _transportSame, _routeSame, provenancePkg, _namePkg⟩
  have observationUnary : UnaryHistory observation :=
    unary_cont_closed sequenceUnary windowUnary observationCont
  have admittedUnary : UnaryHistory admitted :=
    unary_cont_closed observationUnary dyadicUnary admittedCont
  exact
    ⟨sequenceUnary, windowUnary, dyadicUnary, observationUnary, admittedUnary,
      observationCont, admittedCont, provenancePkg, admittedPkg⟩

end BEDC.Derived.RealSequenceLimitUp
