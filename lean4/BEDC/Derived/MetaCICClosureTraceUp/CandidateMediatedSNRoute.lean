import BEDC.Derived.MetaCICClosureTraceUp

namespace BEDC.Derived.MetaCICClosureTraceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICClosureTraceCarrier_candidate_mediated_sn_route
    [AskSetup] [PackageSetup] {S U V B R G K H C P N forwarded snRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICClosureTraceCarrier S U V B R G K H C P N bundle pkg ->
      Cont (append (append S U) G) (append B R) forwarded ->
        Cont forwarded K snRead ->
          PkgSig bundle forwarded pkg ->
            PkgSig bundle snRead pkg ->
              UnaryHistory forwarded ∧ UnaryHistory snRead ∧
                Cont (append (append S U) G) (append B R) forwarded ∧
                  Cont forwarded K snRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle forwarded pkg ∧ PkgSig bundle snRead pkg ∧
                      (exists generatorRead : BHist, exists betaRead : BHist,
                        exists frontierRead : BHist,
                          UnaryHistory generatorRead ∧ UnaryHistory betaRead ∧
                            UnaryHistory frontierRead ∧
                              hsame generatorRead (append (append S U) G) ∧
                                hsame betaRead (append B R) ∧
                                  hsame frontierRead
                                    (append (append generatorRead betaRead) K)) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier forwardedRoute snReadRoute forwardedPkg snReadPkg
  obtain ⟨SUnary, UUnary, _VUnary, BUnary, RUnary, GUnary, KUnary, _HUnary,
    _CUnary, _PUnary, _NUnary, _shiftSubstitution, _generatorPackage, _betaRoute,
    pkgSig⟩ := carrier
  let generatorRead := append (append S U) G
  let betaRead := append B R
  let frontierRead := append (append generatorRead betaRead) K
  have SUUnary : UnaryHistory (append S U) :=
    unary_append_closed SUnary UUnary
  have generatorUnary : UnaryHistory generatorRead :=
    unary_append_closed SUUnary GUnary
  have betaUnary : UnaryHistory betaRead :=
    unary_append_closed BUnary RUnary
  have generatorBetaUnary : UnaryHistory (append generatorRead betaRead) :=
    unary_append_closed generatorUnary betaUnary
  have frontierUnary : UnaryHistory frontierRead :=
    unary_append_closed generatorBetaUnary KUnary
  have forwardedUnary : UnaryHistory forwarded :=
    unary_cont_closed generatorUnary betaUnary forwardedRoute
  have snReadUnary : UnaryHistory snRead :=
    unary_cont_closed forwardedUnary KUnary snReadRoute
  exact
    ⟨forwardedUnary, snReadUnary, forwardedRoute, snReadRoute, pkgSig, forwardedPkg,
      snReadPkg, generatorRead, betaRead, frontierRead, generatorUnary, betaUnary,
      frontierUnary, hsame_refl generatorRead, hsame_refl betaRead,
      hsame_refl frontierRead⟩

end BEDC.Derived.MetaCICClosureTraceUp
