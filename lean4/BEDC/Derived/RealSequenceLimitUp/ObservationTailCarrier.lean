import BEDC.Derived.RealSequenceLimitUp.NameCertObligations

namespace BEDC.Derived.RealSequenceLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealSequenceLimitObservationTailCarrier [AskSetup] [PackageSetup]
    {sequenceRow limitRow windowSchedule dyadicLedger classifierRow transport route provenance
      name observation : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealSequenceLimitCarrier sequenceRow limitRow windowSchedule dyadicLedger classifierRow
        transport route provenance name bundle pkg →
      Cont sequenceRow windowSchedule observation →
        PkgSig bundle observation pkg →
          UnaryHistory sequenceRow ∧ UnaryHistory limitRow ∧ UnaryHistory windowSchedule ∧
            UnaryHistory dyadicLedger ∧ UnaryHistory observation ∧
              Cont sequenceRow windowSchedule observation ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle observation pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier observationCont observationPkg
  rcases carrier with
    ⟨sequenceUnary, limitUnary, windowUnary, dyadicUnary, _classifierUnary, _transportUnary,
      _routeUnary, _provenanceUnary, _nameUnary, _routeCont, _classifierCont, _transportSame,
      _routeSame, provenancePkg, _namePkg⟩
  have observationUnary : UnaryHistory observation :=
    unary_cont_closed sequenceUnary windowUnary observationCont
  exact
    ⟨sequenceUnary, limitUnary, windowUnary, dyadicUnary, observationUnary, observationCont,
      provenancePkg, observationPkg⟩

end BEDC.Derived.RealSequenceLimitUp
