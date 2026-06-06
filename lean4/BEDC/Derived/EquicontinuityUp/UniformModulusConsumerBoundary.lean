import BEDC.Derived.EquicontinuityUp

namespace BEDC.Derived.EquicontinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EquicontinuityCarrier_uniform_modulus_consumer_boundary [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead modulusRead finiteBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      UnaryHistory M ->
        UnaryHistory T ->
          Cont handoffRead M modulusRead ->
            Cont modulusRead T finiteBoundary ->
              PkgSig bundle finiteBoundary pkg ->
                UnaryHistory radiusRead ∧ UnaryHistory handoffRead ∧
                  UnaryHistory modulusRead ∧ UnaryHistory finiteBoundary ∧
                    Cont K F radiusRead ∧ Cont radiusRead rho handoffRead ∧
                      Cont handoffRead M modulusRead ∧
                        Cont modulusRead T finiteBoundary ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle finiteBoundary pkg := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle PkgSig Cont UnaryHistory
  intro carrier unaryM unaryT handoffModulus modulusFinite finitePkg
  obtain ⟨radiusUnary, handoffUnary, radiusRoute, handoffRoute, pkgP, _pkgN⟩ :=
    EquicontinuityCarrier_shared_radius_stability carrier
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed handoffUnary unaryM handoffModulus
  have finiteBoundaryUnary : UnaryHistory finiteBoundary :=
    unary_cont_closed modulusUnary unaryT modulusFinite
  exact
    ⟨radiusUnary, handoffUnary, modulusUnary, finiteBoundaryUnary, radiusRoute,
      handoffRoute, handoffModulus, modulusFinite, pkgP, finitePkg⟩

end BEDC.Derived.EquicontinuityUp
