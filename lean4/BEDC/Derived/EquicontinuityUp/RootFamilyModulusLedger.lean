import BEDC.Derived.EquicontinuityUp

namespace BEDC.Derived.EquicontinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EquicontinuityRootFamilyModulusLedger [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead modulusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      UnaryHistory M ->
        Cont radiusRead rho modulusRead ->
          Cont modulusRead M handoffRead ->
            PkgSig bundle P pkg ->
              UnaryHistory K ∧ UnaryHistory F ∧ UnaryHistory rho ∧
                UnaryHistory radiusRead ∧ UnaryHistory modulusRead ∧
                  UnaryHistory handoffRead ∧ Cont K F radiusRead ∧
                    Cont radiusRead rho modulusRead ∧ Cont modulusRead M handoffRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle PkgSig Cont UnaryHistory
  intro carrier unaryM radiusModulus modulusHandoff _pkgPInput
  obtain ⟨unaryK, unaryF, unaryRho, _unaryR, _unaryN, radiusRoute, _storedHandoff,
    pkgP, pkgN⟩ := carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed unaryK unaryF radiusRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed radiusUnary unaryRho radiusModulus
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed modulusUnary unaryM modulusHandoff
  exact
    ⟨unaryK, unaryF, unaryRho, radiusUnary, modulusUnary, handoffUnary, radiusRoute,
      radiusModulus, modulusHandoff, pkgP, pkgN⟩

end BEDC.Derived.EquicontinuityUp
