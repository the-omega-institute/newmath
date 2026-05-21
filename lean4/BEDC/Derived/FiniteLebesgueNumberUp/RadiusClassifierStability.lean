import BEDC.Derived.FiniteLebesgueNumberUp

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

end BEDC.Derived.FiniteLebesgueNumberUp
