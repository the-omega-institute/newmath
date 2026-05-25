import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberCarrier_continuousmap_uniform_route_row [AskSetup]
    [PackageSetup]
    {cover window radius mesh transport route provenance nameRow modulus continuousRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont radius route modulus ->
        Cont modulus transport continuousRead ->
          PkgSig bundle continuousRead pkg ->
            UnaryHistory radius ∧ UnaryHistory route ∧ UnaryHistory modulus ∧
              UnaryHistory continuousRead ∧ Cont radius route modulus ∧
                Cont modulus transport continuousRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle continuousRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier radiusRouteModulus modulusTransportContinuous continuousPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, _meshUnary, transportUnary, routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have modulusUnary : UnaryHistory modulus :=
    unary_cont_closed radiusUnary routeUnary radiusRouteModulus
  have continuousUnary : UnaryHistory continuousRead :=
    unary_cont_closed modulusUnary transportUnary modulusTransportContinuous
  exact
    ⟨radiusUnary, routeUnary, modulusUnary, continuousUnary, radiusRouteModulus,
      modulusTransportContinuous, provenancePkg, continuousPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
