import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberCoverShrinkageStability [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow foldedRadius coverCell
      shrunkenCell : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont window radius foldedRadius ->
        Cont foldedRadius mesh coverCell ->
          Cont coverCell route shrunkenCell ->
            PkgSig bundle shrunkenCell pkg ->
              UnaryHistory foldedRadius ∧ UnaryHistory coverCell ∧
                UnaryHistory shrunkenCell ∧ Cont window radius foldedRadius ∧
                  Cont foldedRadius mesh coverCell ∧ Cont coverCell route shrunkenCell ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle shrunkenCell pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier windowRadiusFold foldedMeshCover coverRouteShrink shrunkenPkg
  obtain ⟨_coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have foldedUnary : UnaryHistory foldedRadius :=
    unary_cont_closed windowUnary radiusUnary windowRadiusFold
  have coverCellUnary : UnaryHistory coverCell :=
    unary_cont_closed foldedUnary meshUnary foldedMeshCover
  have shrunkenUnary : UnaryHistory shrunkenCell :=
    unary_cont_closed coverCellUnary routeUnary coverRouteShrink
  exact
    ⟨foldedUnary, coverCellUnary, shrunkenUnary, windowRadiusFold, foldedMeshCover,
      coverRouteShrink, provenancePkg, shrunkenPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
