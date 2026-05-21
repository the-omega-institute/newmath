import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberRootRadiusChoiceFreeTailExhaustion [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow tailRead realRead
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont radius mesh tailRead ->
        Cont tailRead route realRead ->
          Cont realRead nameRow consumerRead ->
            PkgSig bundle consumerRead pkg ->
              UnaryHistory tailRead ∧ UnaryHistory realRead ∧ UnaryHistory consumerRead ∧
                Cont radius mesh tailRead ∧ Cont tailRead route realRead ∧
                  Cont realRead nameRow consumerRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier radiusMeshTail tailRouteReal realNameConsumer consumerPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed radiusUnary meshUnary radiusMeshTail
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary routeUnary tailRouteReal
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed realUnary nameRowUnary realNameConsumer
  exact
    ⟨tailUnary, realUnary, consumerUnary, radiusMeshTail, tailRouteReal,
      realNameConsumer, provenancePkg, consumerPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
