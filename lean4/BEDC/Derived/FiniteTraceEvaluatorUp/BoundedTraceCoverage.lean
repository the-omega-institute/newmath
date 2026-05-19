import BEDC.Derived.FiniteTraceEvaluatorUp.NameCertObligations

namespace BEDC.Derived.FiniteTraceEvaluatorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteTraceEvaluatorCarrier_bounded_trace_coverage [AskSetup] [PackageSetup]
    {input trace accepted validation transport route provenance localRow traceRead
      acceptedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTraceEvaluatorCarrier input trace accepted validation transport route provenance
        localRow bundle pkg →
      Cont input trace traceRead →
        Cont traceRead accepted acceptedRead →
          UnaryHistory input ∧ UnaryHistory trace ∧ UnaryHistory accepted ∧
            UnaryHistory traceRead ∧ UnaryHistory acceptedRead ∧
              Cont input trace traceRead ∧ Cont traceRead accepted acceptedRead ∧
                hsame transport (append input accepted) ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro carrier traceRoute acceptedRoute
  obtain ⟨inputUnary, traceUnary, acceptedUnary, _validationUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _localRowUnary, _inputTraceRoute,
    _routeAcceptedLocal, _acceptedValidationProvenance, transportSame, provenancePkg⟩ :=
    carrier
  have traceReadUnary : UnaryHistory traceRead :=
    unary_cont_closed inputUnary traceUnary traceRoute
  have acceptedReadUnary : UnaryHistory acceptedRead :=
    unary_cont_closed traceReadUnary acceptedUnary acceptedRoute
  exact
    ⟨inputUnary, traceUnary, acceptedUnary, traceReadUnary, acceptedReadUnary,
      traceRoute, acceptedRoute, transportSame, provenancePkg⟩

end BEDC.Derived.FiniteTraceEvaluatorUp
