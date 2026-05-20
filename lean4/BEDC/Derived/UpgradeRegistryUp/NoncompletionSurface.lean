import BEDC.Derived.UpgradeRegistryUp.NameCertObligations

namespace BEDC.Derived.UpgradeRegistryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UpgradeRegistryNoncompletionSurface [AskSetup] [PackageSetup]
    {T S Nx F B A R H C P L nextRead blockerRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S -> UnaryHistory Nx -> UnaryHistory F -> UnaryHistory B ->
      UnaryHistory C -> UnaryHistory L -> Cont S Nx nextRead ->
        Cont F B blockerRead -> Cont C L namedRead -> PkgSig bundle namedRead pkg ->
          UnaryHistory nextRead ∧ UnaryHistory blockerRead ∧ UnaryHistory namedRead ∧
            Cont S Nx nextRead ∧ Cont F B blockerRead ∧ PkgSig bundle namedRead pkg ∧
              upgradeRegistryFields (UpgradeRegistryUp.mk T S Nx F B A R H C P L) =
                [T, S, Nx, F, B, A, R, H, C, P, L] := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro statusUnary nextUnary fieldUnary blockerUnary continuationUnary localUnary
    nextCont blockerCont namedCont namedPkg
  have nextReadUnary : UnaryHistory nextRead :=
    unary_cont_closed statusUnary nextUnary nextCont
  have blockerReadUnary : UnaryHistory blockerRead :=
    unary_cont_closed fieldUnary blockerUnary blockerCont
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed continuationUnary localUnary namedCont
  exact
    ⟨nextReadUnary, blockerReadUnary, namedReadUnary, nextCont, blockerCont,
      namedPkg, rfl⟩

end BEDC.Derived.UpgradeRegistryUp
