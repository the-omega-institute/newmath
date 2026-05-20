import BEDC.Derived.DiagonalCofinalTailUp

namespace BEDC.Derived.DiagonalCofinalTailUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalCofinalTailCarrier_compatibility_handoff [AskSetup] [PackageSetup]
    {q s g d r w h c p n streamRead tailRead realRead compatibilityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalCofinalTailCarrier q s g d r w h c p n bundle pkg ->
      Cont s g streamRead ->
        Cont streamRead r tailRead ->
          Cont r w realRead ->
            Cont tailRead c compatibilityRead ->
              PkgSig bundle compatibilityRead pkg ->
                UnaryHistory q ∧ UnaryHistory s ∧ UnaryHistory g ∧ UnaryHistory d ∧
                  UnaryHistory r ∧ UnaryHistory w ∧ UnaryHistory streamRead ∧
                    UnaryHistory tailRead ∧ UnaryHistory realRead ∧
                      UnaryHistory compatibilityRead ∧ Cont q s g ∧ Cont g d r ∧
                        Cont s g streamRead ∧ Cont streamRead r tailRead ∧
                          Cont r w realRead ∧ Cont tailRead c compatibilityRead ∧
                            PkgSig bundle p pkg ∧ PkgSig bundle compatibilityRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory DiagonalCofinalTailCarrier
  intro carrier streamRoute tailRoute realRoute compatibilityRoute compatibilityPkg
  obtain ⟨qUnary, sUnary, gUnary, dUnary, rUnary, wUnary, _hUnary, cUnary,
    _pUnary, _nUnary, qsRoute, gdRoute, _whRoute, pPkg⟩ := carrier
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed sUnary gUnary streamRoute
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed streamUnary rUnary tailRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed rUnary wUnary realRoute
  have compatibilityUnary : UnaryHistory compatibilityRead :=
    unary_cont_closed tailUnary cUnary compatibilityRoute
  exact
    ⟨qUnary, sUnary, gUnary, dUnary, rUnary, wUnary, streamUnary, tailUnary,
      realUnary, compatibilityUnary, qsRoute, gdRoute, streamRoute, tailRoute,
      realRoute, compatibilityRoute, pPkg, compatibilityPkg⟩

end BEDC.Derived.DiagonalCofinalTailUp
