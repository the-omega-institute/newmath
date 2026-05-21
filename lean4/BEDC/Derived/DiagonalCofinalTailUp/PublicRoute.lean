import BEDC.Derived.DiagonalCofinalTailUp

namespace BEDC.Derived.DiagonalCofinalTailUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalCofinalTailCarrier_public_route [AskSetup] [PackageSetup]
    {q s g d r w h c p n streamRead dyadicRead realRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalCofinalTailCarrier q s g d r w h c p n bundle pkg ->
      Cont s g streamRead ->
        Cont streamRead d dyadicRead ->
          Cont dyadicRead r realRead ->
            Cont realRead c publicRead ->
              PkgSig bundle publicRead pkg ->
                UnaryHistory q ∧ UnaryHistory s ∧ UnaryHistory g ∧ UnaryHistory d ∧
                  UnaryHistory r ∧ UnaryHistory w ∧ UnaryHistory streamRead ∧
                    UnaryHistory dyadicRead ∧ UnaryHistory realRead ∧
                      UnaryHistory publicRead ∧ Cont q s g ∧ Cont g d r ∧
                        Cont s g streamRead ∧ Cont streamRead d dyadicRead ∧
                          Cont dyadicRead r realRead ∧ Cont realRead c publicRead ∧
                            PkgSig bundle p pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier streamRoute dyadicRoute realRoute publicRoute publicPkg
  obtain ⟨qUnary, sUnary, gUnary, dUnary, rUnary, wUnary, _hUnary, cUnary,
    _pUnary, _nUnary, qsRoute, gdRoute, _whRoute, pPkg⟩ := carrier
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed sUnary gUnary streamRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed streamUnary dUnary dyadicRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed dyadicUnary rUnary realRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed realUnary cUnary publicRoute
  exact
    ⟨qUnary, sUnary, gUnary, dUnary, rUnary, wUnary, streamUnary, dyadicUnary,
      realUnary, publicUnary, qsRoute, gdRoute, streamRoute, dyadicRoute, realRoute,
      publicRoute, pPkg, publicPkg⟩

end BEDC.Derived.DiagonalCofinalTailUp
