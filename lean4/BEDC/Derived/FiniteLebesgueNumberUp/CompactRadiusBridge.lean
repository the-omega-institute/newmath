import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem FiniteLebesgueNumberCompactRadiusBridge [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow compactNet : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont cover radius compactNet ->
        PkgSig bundle compactNet pkg ->
          hsame radius radius ∧ Cont cover radius compactNet ∧
            PkgSig bundle compactNet pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg PkgSig
  intro carrier coverRadiusCompact compactPkg
  obtain ⟨_coverUnary, _windowUnary, _radiusUnary, _meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  exact ⟨hsame_refl radius, coverRadiusCompact, compactPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
