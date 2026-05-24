import BEDC.Derived.RealSequenceLimitUp.NameCertObligations

namespace BEDC.Derived.RealSequenceLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealSequenceLimitLimitModulusComposition [AskSetup] [PackageSetup]
    {sequenceRow limitRow windowSchedule dyadicLedger classifierRow transport route provenance
      name threshold admitted exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealSequenceLimitCarrier sequenceRow limitRow windowSchedule dyadicLedger classifierRow
        transport route provenance name bundle pkg ->
      Cont dyadicLedger windowSchedule threshold ->
        Cont threshold classifierRow admitted ->
          Cont admitted route exported ->
            PkgSig bundle exported pkg ->
              UnaryHistory dyadicLedger ∧ UnaryHistory windowSchedule ∧
                UnaryHistory threshold ∧ UnaryHistory admitted ∧ UnaryHistory exported ∧
                  Cont dyadicLedger windowSchedule threshold ∧
                    Cont threshold classifierRow admitted ∧ Cont admitted route exported ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle exported pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier thresholdCont admittedCont exportedCont exportedPkg
  rcases carrier with
    ⟨_sequenceUnary, _limitUnary, windowUnary, dyadicUnary, classifierUnary, _transportUnary,
      routeUnary, _provenanceUnary, _nameUnary, _routeCont, _classifierCont, _transportSame,
      _routeSame, provenancePkg, _namePkg⟩
  have thresholdUnary : UnaryHistory threshold :=
    unary_cont_closed dyadicUnary windowUnary thresholdCont
  have admittedUnary : UnaryHistory admitted :=
    unary_cont_closed thresholdUnary classifierUnary admittedCont
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed admittedUnary routeUnary exportedCont
  exact
    ⟨dyadicUnary, windowUnary, thresholdUnary, admittedUnary, exportedUnary, thresholdCont,
      admittedCont, exportedCont, provenancePkg, exportedPkg⟩

end BEDC.Derived.RealSequenceLimitUp
