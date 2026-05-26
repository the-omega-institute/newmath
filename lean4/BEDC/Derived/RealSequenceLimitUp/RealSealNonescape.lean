import BEDC.Derived.RealSequenceLimitUp.NameCertObligations

namespace BEDC.Derived.RealSequenceLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealSequenceLimitRealSealNonescape [AskSetup] [PackageSetup]
    {sequenceRow limitRow windowSchedule dyadicLedger classifierRow transport route provenance
      name observation threshold admitted realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealSequenceLimitCarrier sequenceRow limitRow windowSchedule dyadicLedger classifierRow
        transport route provenance name bundle pkg ->
      Cont sequenceRow windowSchedule observation ->
        Cont dyadicLedger windowSchedule threshold ->
          Cont threshold classifierRow admitted ->
            Cont admitted realSeal route ->
              PkgSig bundle route pkg ->
                UnaryHistory observation ∧ UnaryHistory threshold ∧ UnaryHistory admitted ∧
                  Cont sequenceRow windowSchedule observation ∧
                    Cont dyadicLedger windowSchedule threshold ∧
                      Cont threshold classifierRow admitted ∧ Cont admitted realSeal route ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle route pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier observationCont thresholdCont admittedCont realSealCont routePkg
  rcases carrier with
    ⟨sequenceUnary, _limitUnary, windowUnary, dyadicUnary, classifierUnary, _transportUnary,
      _routeUnary, _provenanceUnary, _nameUnary, _routeCont, _classifierCont, _transportSame,
      _routeSame, provenancePkg, _namePkg⟩
  have observationUnary : UnaryHistory observation :=
    unary_cont_closed sequenceUnary windowUnary observationCont
  have thresholdUnary : UnaryHistory threshold :=
    unary_cont_closed dyadicUnary windowUnary thresholdCont
  have admittedUnary : UnaryHistory admitted :=
    unary_cont_closed thresholdUnary classifierUnary admittedCont
  exact
    ⟨observationUnary, thresholdUnary, admittedUnary, observationCont, thresholdCont,
      admittedCont, realSealCont, provenancePkg, routePkg⟩

end BEDC.Derived.RealSequenceLimitUp
