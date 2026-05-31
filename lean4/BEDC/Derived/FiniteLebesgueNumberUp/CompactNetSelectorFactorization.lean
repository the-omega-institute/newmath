import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberCompactNetSelectorFactorization [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow compactRead selectorRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont radius mesh compactRead ->
        Cont compactRead nameRow selectorRead ->
          PkgSig bundle selectorRead pkg ->
            UnaryHistory radius ∧ UnaryHistory compactRead ∧ UnaryHistory selectorRead ∧
              Cont radius mesh compactRead ∧ Cont compactRead nameRow selectorRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle selectorRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier radiusMeshCompact compactNameSelector selectorPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed radiusUnary meshUnary radiusMeshCompact
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed compactUnary nameRowUnary compactNameSelector
  exact
    ⟨radiusUnary, compactUnary, selectorUnary, radiusMeshCompact, compactNameSelector,
      provenancePkg, selectorPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
