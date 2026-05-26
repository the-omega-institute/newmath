import BEDC.Derived.RealSequenceLimitUp.NameCertObligations

namespace BEDC.Derived.RealSequenceLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealSequenceLimitTailWindowTransport [AskSetup] [PackageSetup]
    {sequenceRow limitRow windowSchedule dyadicLedger classifierRow transport route provenance
      name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealSequenceLimitCarrier sequenceRow limitRow windowSchedule dyadicLedger classifierRow
        transport route provenance name bundle pkg ->
      Cont windowSchedule dyadicLedger endpoint ->
        PkgSig bundle endpoint pkg ->
          UnaryHistory sequenceRow ∧ UnaryHistory limitRow ∧ UnaryHistory windowSchedule ∧
            UnaryHistory dyadicLedger ∧ UnaryHistory endpoint ∧
              Cont sequenceRow windowSchedule route ∧ Cont windowSchedule dyadicLedger endpoint ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier endpointCont endpointPkg
  rcases carrier with
    ⟨sequenceUnary, limitUnary, windowUnary, dyadicUnary, _classifierUnary, _transportUnary,
      _routeUnary, _provenanceUnary, _nameUnary, routeCont, _classifierCont, _transportSame,
      _routeSame, provenancePkg, _namePkg⟩
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed windowUnary dyadicUnary endpointCont
  exact
    ⟨sequenceUnary, limitUnary, windowUnary, dyadicUnary, endpointUnary, routeCont,
      endpointCont, provenancePkg, endpointPkg⟩

end BEDC.Derived.RealSequenceLimitUp
