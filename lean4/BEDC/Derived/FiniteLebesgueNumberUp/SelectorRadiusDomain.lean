import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberSelectorRadiusDomain [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow selectorRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont radius mesh selectorRead ->
        PkgSig bundle selectorRead pkg ->
          UnaryHistory radius ∧ UnaryHistory mesh ∧ UnaryHistory selectorRead ∧
            Cont radius mesh selectorRead ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle selectorRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier radiusMeshSelector selectorPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed radiusUnary meshUnary radiusMeshSelector
  exact
    ⟨radiusUnary, meshUnary, selectorUnary, radiusMeshSelector, provenancePkg, selectorPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
