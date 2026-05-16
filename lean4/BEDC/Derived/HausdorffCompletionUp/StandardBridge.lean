import BEDC.Derived.HausdorffCompletionUp

namespace BEDC.Derived.HausdorffCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HausdorffCompletionCarrier_standard_bridge_source_packet [AskSetup] [PackageSetup]
    {source entourage separated handoff transport route provenance bridgeSource : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HausdorffCompletionCarrier source entourage separated handoff transport route provenance
        bundle pkg ->
      Cont source handoff bridgeSource ->
        PkgSig bundle bridgeSource pkg ->
          UnaryHistory source ∧ UnaryHistory entourage ∧ UnaryHistory separated ∧
            UnaryHistory handoff ∧ UnaryHistory transport ∧ UnaryHistory route ∧
              UnaryHistory provenance ∧ UnaryHistory bridgeSource ∧
                Cont source entourage transport ∧ Cont separated handoff route ∧
                  Cont transport route provenance ∧ Cont source handoff bridgeSource ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle bridgeSource pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg
  intro carrier sourceHandoffBridgeSource bridgeSourcePkg
  obtain ⟨sourceUnary, entourageUnary, separatedUnary, handoffUnary, transportUnary,
    routeUnary, provenanceUnary, sourceEntourageTransport, separatedHandoffRoute,
    transportRouteProvenance, provenancePkg⟩ := carrier
  have bridgeSourceUnary : UnaryHistory bridgeSource :=
    unary_cont_closed sourceUnary handoffUnary sourceHandoffBridgeSource
  exact
    ⟨sourceUnary, entourageUnary, separatedUnary, handoffUnary, transportUnary, routeUnary,
      provenanceUnary, bridgeSourceUnary, sourceEntourageTransport, separatedHandoffRoute,
      transportRouteProvenance, sourceHandoffBridgeSource, provenancePkg, bridgeSourcePkg⟩

end BEDC.Derived.HausdorffCompletionUp
