import BEDC.Derived.EquicontinuityUp

namespace BEDC.Derived.EquicontinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EquicontinuityRootUnblockSharedRadiusHandoff [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead sharedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      UnaryHistory M ->
        Cont handoffRead M sharedRead ->
          PkgSig bundle sharedRead pkg ->
            UnaryHistory rho ∧ UnaryHistory handoffRead ∧ UnaryHistory sharedRead ∧
              Cont K F radiusRead ∧ Cont radiusRead rho handoffRead ∧
                Cont handoffRead M sharedRead ∧ PkgSig bundle sharedRead pkg := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier unaryM sharedRoute sharedPkg
  obtain ⟨_radiusUnary, handoffUnary, radiusRoute, handoffRoute, _pkgP, _pkgN⟩ :=
    EquicontinuityCarrier_shared_radius_stability carrier
  obtain ⟨_unaryK, _unaryF, unaryRho, _unaryR, _unaryN, _radiusRoute,
    _handoffRoute, _pkgP2, _pkgN2⟩ := carrier
  have sharedUnary : UnaryHistory sharedRead :=
    unary_cont_closed handoffUnary unaryM sharedRoute
  exact
    ⟨unaryRho, handoffUnary, sharedUnary, radiusRoute, handoffRoute, sharedRoute,
      sharedPkg⟩

end BEDC.Derived.EquicontinuityUp
