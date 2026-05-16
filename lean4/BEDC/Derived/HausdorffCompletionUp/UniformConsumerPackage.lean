import BEDC.Derived.HausdorffCompletionUp

namespace BEDC.Derived.HausdorffCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HausdorffCompletionCarrier_uniform_consumer_package [AskSetup] [PackageSetup]
    {source entourage separated handoff transport route provenance consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HausdorffCompletionCarrier source entourage separated handoff transport route provenance
        bundle pkg ->
      Cont entourage handoff consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory source ∧ UnaryHistory entourage ∧ UnaryHistory separated ∧
            UnaryHistory handoff ∧ UnaryHistory transport ∧ UnaryHistory route ∧
              UnaryHistory provenance ∧ UnaryHistory consumer ∧
                Cont source entourage transport ∧ Cont separated handoff route ∧
                  Cont transport route provenance ∧ Cont entourage handoff consumer ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg
  intro carrier entourageHandoffConsumer consumerPkg
  obtain ⟨sourceUnary, entourageUnary, separatedUnary, handoffUnary, transportUnary,
    routeUnary, provenanceUnary, sourceEntourageTransport, separatedHandoffRoute,
    transportRouteProvenance, provenancePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed entourageUnary handoffUnary entourageHandoffConsumer
  exact
    ⟨sourceUnary, entourageUnary, separatedUnary, handoffUnary, transportUnary,
      routeUnary, provenanceUnary, consumerUnary, sourceEntourageTransport,
      separatedHandoffRoute, transportRouteProvenance, entourageHandoffConsumer,
      provenancePkg, consumerPkg⟩

end BEDC.Derived.HausdorffCompletionUp
