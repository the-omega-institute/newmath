import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberRadiusClassifierStability [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow radius' mesh' route' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      hsame radius radius' ->
        hsame mesh mesh' ->
          Cont radius' mesh' route' ->
            UnaryHistory radius' ∧ UnaryHistory mesh' ∧ UnaryHistory route' ∧
              Cont radius' mesh' route' ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier sameRadius sameMesh transportedRoute
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have radiusPrimeUnary : UnaryHistory radius' := unary_transport radiusUnary sameRadius
  have meshPrimeUnary : UnaryHistory mesh' := unary_transport meshUnary sameMesh
  have routePrimeUnary : UnaryHistory route' :=
    unary_cont_closed radiusPrimeUnary meshPrimeUnary transportedRoute
  exact
    ⟨radiusPrimeUnary, meshPrimeUnary, routePrimeUnary, transportedRoute, provenancePkg⟩

theorem FiniteLebesgueNumberOpenPhaseRootRadiusClassifierTotality [AskSetup]
    [PackageSetup]
    {cover window radius mesh transport route provenance nameRow rootRead phaseRead
      classifierRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont route nameRow rootRead ->
        Cont rootRead radius phaseRead ->
          Cont phaseRead mesh classifierRead ->
            Cont classifierRead nameRow consumerRead ->
              PkgSig bundle consumerRead pkg ->
                UnaryHistory classifierRead ∧ UnaryHistory consumerRead ∧
                  Cont phaseRead mesh classifierRead ∧
                    Cont classifierRead nameRow consumerRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier routeNameRoot rootRadiusPhase phaseMeshClassifier classifierNameConsumer
    consumerPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameRoot
  have phaseReadUnary : UnaryHistory phaseRead :=
    unary_cont_closed rootReadUnary radiusUnary rootRadiusPhase
  have classifierReadUnary : UnaryHistory classifierRead :=
    unary_cont_closed phaseReadUnary meshUnary phaseMeshClassifier
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed classifierReadUnary nameRowUnary classifierNameConsumer
  exact
    ⟨classifierReadUnary, consumerReadUnary, phaseMeshClassifier, classifierNameConsumer,
      provenancePkg, consumerPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
