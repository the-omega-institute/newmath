import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberOpenPhaseRootUnblockConsumerReadback [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow phaseRead endpointRead
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont cover window phaseRead ->
        Cont phaseRead radius endpointRead ->
          Cont endpointRead nameRow consumerRead ->
            PkgSig bundle consumerRead pkg ->
              UnaryHistory phaseRead ∧ UnaryHistory endpointRead ∧
                UnaryHistory consumerRead ∧ Cont cover window phaseRead ∧
                  Cont phaseRead radius endpointRead ∧ Cont endpointRead nameRow consumerRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier coverWindowPhase phaseRadiusEndpoint endpointNameConsumer consumerPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, _meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed coverUnary windowUnary coverWindowPhase
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed phaseUnary radiusUnary phaseRadiusEndpoint
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed endpointUnary nameRowUnary endpointNameConsumer
  exact
    ⟨phaseUnary, endpointUnary, consumerUnary, coverWindowPhase, phaseRadiusEndpoint,
      endpointNameConsumer, provenancePkg, consumerPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
