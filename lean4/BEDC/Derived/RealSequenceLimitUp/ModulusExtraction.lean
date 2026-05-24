import BEDC.Derived.RealSequenceLimitUp.NameCertObligations

namespace BEDC.Derived.RealSequenceLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealSequenceLimitModulusExtraction [AskSetup] [PackageSetup]
    {sequenceRow limitRow windowSchedule dyadicLedger classifierRow transport route provenance
      name threshold admitted : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealSequenceLimitCarrier sequenceRow limitRow windowSchedule dyadicLedger classifierRow
        transport route provenance name bundle pkg ->
      Cont dyadicLedger windowSchedule threshold ->
        Cont threshold classifierRow admitted ->
          PkgSig bundle admitted pkg ->
            UnaryHistory dyadicLedger ∧ UnaryHistory windowSchedule ∧ UnaryHistory threshold ∧
              UnaryHistory classifierRow ∧ UnaryHistory admitted ∧
                Cont dyadicLedger windowSchedule threshold ∧
                  Cont threshold classifierRow admitted ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle admitted pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier thresholdCont admittedCont admittedPkg
  rcases carrier with
    ⟨_sequenceUnary, _limitUnary, windowUnary, dyadicUnary, classifierUnary, _transportUnary,
      _routeUnary, _provenanceUnary, _nameUnary, _routeCont, _classifierCont, _transportSame,
      _routeSame, provenancePkg, _namePkg⟩
  have thresholdUnary : UnaryHistory threshold :=
    unary_cont_closed dyadicUnary windowUnary thresholdCont
  have admittedUnary : UnaryHistory admitted :=
    unary_cont_closed thresholdUnary classifierUnary admittedCont
  exact
    ⟨dyadicUnary, windowUnary, thresholdUnary, classifierUnary, admittedUnary, thresholdCont,
      admittedCont, provenancePkg, admittedPkg⟩

end BEDC.Derived.RealSequenceLimitUp
