import BEDC.Derived.KernelMorphismUp

namespace BEDC.Derived.KernelMorphismUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KernelMorphismCarrier_scoped_consumer_packet [AskSetup] [PackageSetup]
    {source target graph edgeAdmission classifierLift transport route provenance cert endpoint
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelMorphismEdgeLiftCarrier source target graph edgeAdmission classifierLift transport
        route provenance cert endpoint bundle pkg →
      Cont endpoint cert consumerRead →
        PkgSig bundle consumerRead pkg →
          UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧
            UnaryHistory endpoint ∧ UnaryHistory consumerRead ∧
              Cont source edgeAdmission target ∧ Cont target classifierLift graph ∧
                Cont graph route endpoint ∧ Cont endpoint cert consumerRead ∧
                  PkgSig bundle endpoint pkg ∧ PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier endpointCertConsumer consumerPkg
  obtain ⟨sourceUnary, targetUnary, graphUnary, _admissionUnary, _liftUnary,
    _transportUnary, _routeUnary, _provenanceUnary, certUnary, endpointUnary,
    sourceAdmissionTarget, targetLiftGraph, graphRouteEndpoint, endpointPkg⟩ := carrier
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed endpointUnary certUnary endpointCertConsumer
  exact
    ⟨sourceUnary, targetUnary, graphUnary, endpointUnary, consumerUnary,
      sourceAdmissionTarget, targetLiftGraph, graphRouteEndpoint, endpointCertConsumer,
      endpointPkg, consumerPkg⟩

end BEDC.Derived.KernelMorphismUp
