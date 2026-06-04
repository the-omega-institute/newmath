import BEDC.Derived.EquicontinuityUp

namespace BEDC.Derived.EquicontinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EquicontinuityRootUnblockCompactSourceRow [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead compactRead sourceLocked : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      Cont K F compactRead ->
        Cont compactRead rho sourceLocked ->
          PkgSig bundle sourceLocked pkg ->
            UnaryHistory K ∧ UnaryHistory F ∧ UnaryHistory rho ∧
              UnaryHistory compactRead ∧ UnaryHistory sourceLocked ∧
                Cont K F compactRead ∧ Cont compactRead rho sourceLocked ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle sourceLocked pkg := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier compactRoute sourceRoute sourcePkg
  obtain ⟨unaryK, unaryF, unaryRho, _unaryR, _unaryN, _radiusRoute,
    _handoffRoute, pkgP, _pkgN⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed unaryK unaryF compactRoute
  have sourceUnary : UnaryHistory sourceLocked :=
    unary_cont_closed compactUnary unaryRho sourceRoute
  exact
    ⟨unaryK, unaryF, unaryRho, compactUnary, sourceUnary, compactRoute, sourceRoute,
      pkgP, sourcePkg⟩

end BEDC.Derived.EquicontinuityUp
