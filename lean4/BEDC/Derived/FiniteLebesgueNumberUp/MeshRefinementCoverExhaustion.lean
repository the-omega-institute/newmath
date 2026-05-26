import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberMeshRefinementCoverExhaustion [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow meshRead coverCell : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont mesh route meshRead ->
        Cont meshRead cover coverCell ->
          PkgSig bundle coverCell pkg ->
            hsame mesh mesh ∧ hsame cover cover ∧ Cont meshRead cover coverCell ∧
              PkgSig bundle coverCell pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg PkgSig
  intro carrier meshRouteRead readCoverCell coverCellPkg
  obtain ⟨coverUnary, _windowUnary, _radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  have meshReadUnary : UnaryHistory meshRead :=
    unary_cont_closed meshUnary routeUnary meshRouteRead
  have _coverCellUnary : UnaryHistory coverCell :=
    unary_cont_closed meshReadUnary coverUnary readCoverCell
  exact ⟨hsame_refl mesh, hsame_refl cover, readCoverCell, coverCellPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
