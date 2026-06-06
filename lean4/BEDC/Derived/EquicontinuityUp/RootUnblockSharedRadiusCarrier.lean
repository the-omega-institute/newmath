import BEDC.Derived.EquicontinuityUp

namespace BEDC.Derived.EquicontinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EquicontinuityRootUnblockSharedRadiusCarrier [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead sharedRadiusRoot : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      Cont handoffRead R sharedRadiusRoot ->
        PkgSig bundle sharedRadiusRoot pkg ->
          UnaryHistory radiusRead ∧ UnaryHistory handoffRead ∧
            UnaryHistory sharedRadiusRoot ∧ Cont K F radiusRead ∧
              Cont radiusRead rho handoffRead ∧ Cont handoffRead R sharedRadiusRoot ∧
                PkgSig bundle P pkg ∧ PkgSig bundle sharedRadiusRoot pkg := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier rootRoute rootPkg
  obtain ⟨radiusUnary, handoffUnary, radiusRoute, handoffRoute, pkgP, _pkgN⟩ :=
    EquicontinuityCarrier_shared_radius_stability carrier
  obtain ⟨_unaryK, _unaryF, _unaryRho, unaryR, _unaryN, _radiusRoute,
    _handoffRoute, _carrierPkgP, _carrierPkgN⟩ := carrier
  have rootUnary : UnaryHistory sharedRadiusRoot :=
    unary_cont_closed handoffUnary unaryR rootRoute
  exact
    ⟨radiusUnary, handoffUnary, rootUnary, radiusRoute, handoffRoute, rootRoute, pkgP,
      rootPkg⟩

end BEDC.Derived.EquicontinuityUp
