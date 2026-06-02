import BEDC.Derived.EquicontinuityUp

namespace BEDC.Derived.EquicontinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EquicontinuityFiniteNetReadiness [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead finiteNetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg →
      UnaryHistory M →
        Cont handoffRead M finiteNetRead →
          PkgSig bundle finiteNetRead pkg →
            UnaryHistory radiusRead ∧ UnaryHistory handoffRead ∧
              UnaryHistory finiteNetRead ∧ Cont K F radiusRead ∧
                Cont radiusRead rho handoffRead ∧ Cont handoffRead M finiteNetRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                    PkgSig bundle finiteNetRead pkg := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle PkgSig Cont UnaryHistory
  intro carrier unaryM finiteNetRoute finiteNetPkg
  obtain ⟨radiusUnary, handoffUnary, radiusRoute, handoffRoute, pkgP, pkgN⟩ :=
    EquicontinuityCarrier_shared_radius_stability carrier
  have finiteNetUnary : UnaryHistory finiteNetRead :=
    unary_cont_closed handoffUnary unaryM finiteNetRoute
  exact
    ⟨radiusUnary, handoffUnary, finiteNetUnary, radiusRoute, handoffRoute, finiteNetRoute,
      pkgP, pkgN, finiteNetPkg⟩

end BEDC.Derived.EquicontinuityUp
