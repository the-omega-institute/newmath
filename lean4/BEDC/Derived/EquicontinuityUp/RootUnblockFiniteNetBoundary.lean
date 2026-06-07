import BEDC.Derived.EquicontinuityUp

namespace BEDC.Derived.EquicontinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EquicontinuityRootUnblockFiniteNetBoundary [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead finiteNetRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      UnaryHistory M ->
        Cont handoffRead M finiteNetRead ->
          Cont finiteNetRead R boundaryRead ->
            PkgSig bundle boundaryRead pkg ->
              UnaryHistory K ∧ UnaryHistory F ∧ UnaryHistory rho ∧ UnaryHistory M ∧
                UnaryHistory finiteNetRead ∧ UnaryHistory boundaryRead ∧
                  Cont K F radiusRead ∧ Cont radiusRead rho handoffRead ∧
                    Cont handoffRead M finiteNetRead ∧
                      Cont finiteNetRead R boundaryRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle PkgSig Cont UnaryHistory
  intro carrier unaryM finiteNetRoute boundaryRoute boundaryPkg
  obtain ⟨unaryK, unaryF, unaryRho, unaryR, _unaryN, radiusRoute, handoffRoute, pkgP,
    _pkgN⟩ := carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed unaryK unaryF radiusRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed radiusUnary unaryRho handoffRoute
  have finiteNetUnary : UnaryHistory finiteNetRead :=
    unary_cont_closed handoffUnary unaryM finiteNetRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed finiteNetUnary unaryR boundaryRoute
  exact
    ⟨unaryK, unaryF, unaryRho, unaryM, finiteNetUnary, boundaryUnary, radiusRoute,
      handoffRoute, finiteNetRoute, boundaryRoute, pkgP, boundaryPkg⟩

end BEDC.Derived.EquicontinuityUp
