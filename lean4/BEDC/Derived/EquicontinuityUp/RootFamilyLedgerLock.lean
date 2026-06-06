import BEDC.Derived.EquicontinuityUp

namespace BEDC.Derived.EquicontinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EquicontinuityRootFamilyLedgerLock [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead familyReplay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      UnaryHistory T ->
        Cont F T familyReplay ->
          PkgSig bundle familyReplay pkg ->
            UnaryHistory K ∧ UnaryHistory F ∧ UnaryHistory T ∧
              UnaryHistory radiusRead ∧ UnaryHistory handoffRead ∧
                UnaryHistory familyReplay ∧ Cont K F radiusRead ∧
                  Cont radiusRead rho handoffRead ∧ Cont F T familyReplay ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle familyReplay pkg := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle PkgSig Cont UnaryHistory
  intro carrier unaryT familyRoute familyPkg
  obtain ⟨radiusUnary, handoffUnary, radiusRoute, handoffRoute, pkgP, _pkgN⟩ :=
    EquicontinuityCarrier_shared_radius_stability carrier
  obtain ⟨unaryK, unaryF, _unaryRho, _unaryR, _unaryN, _carrierRadiusRoute,
    _carrierHandoffRoute, _carrierPkgP, _carrierPkgN⟩ := carrier
  have familyUnary : UnaryHistory familyReplay :=
    unary_cont_closed unaryF unaryT familyRoute
  exact
    ⟨unaryK, unaryF, unaryT, radiusUnary, handoffUnary, familyUnary, radiusRoute,
      handoffRoute, familyRoute, pkgP, familyPkg⟩

end BEDC.Derived.EquicontinuityUp
