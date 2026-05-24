import BEDC.Derived.RealSequenceLimitUp.ModulusExtraction

namespace BEDC.Derived.RealSequenceLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealSequenceLimitCauchyModulusHandoff [AskSetup] [PackageSetup]
    {sequenceRow limitRow windowSchedule dyadicLedger classifierRow transport route provenance
      name threshold admitted handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealSequenceLimitCarrier sequenceRow limitRow windowSchedule dyadicLedger classifierRow
        transport route provenance name bundle pkg ->
      Cont dyadicLedger windowSchedule threshold ->
        Cont threshold classifierRow admitted ->
          Cont admitted route handoff ->
            PkgSig bundle handoff pkg ->
              UnaryHistory dyadicLedger ∧ UnaryHistory windowSchedule ∧
                UnaryHistory classifierRow ∧ UnaryHistory threshold ∧ UnaryHistory admitted ∧
                  UnaryHistory handoff ∧ Cont dyadicLedger windowSchedule threshold ∧
                    Cont threshold classifierRow admitted ∧ Cont admitted route handoff ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier thresholdCont admittedCont handoffCont handoffPkg
  rcases carrier with
    ⟨_sequenceUnary, _limitUnary, windowUnary, dyadicUnary, classifierUnary, _transportUnary,
      routeUnary, _provenanceUnary, _nameUnary, _routeCont, _classifierCont, _transportSame,
      _routeSame, provenancePkg, _namePkg⟩
  have thresholdUnary : UnaryHistory threshold :=
    unary_cont_closed dyadicUnary windowUnary thresholdCont
  have admittedUnary : UnaryHistory admitted :=
    unary_cont_closed thresholdUnary classifierUnary admittedCont
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed admittedUnary routeUnary handoffCont
  exact
    ⟨dyadicUnary, windowUnary, classifierUnary, thresholdUnary, admittedUnary, handoffUnary,
      thresholdCont, admittedCont, handoffCont, provenancePkg, handoffPkg⟩

end BEDC.Derived.RealSequenceLimitUp
