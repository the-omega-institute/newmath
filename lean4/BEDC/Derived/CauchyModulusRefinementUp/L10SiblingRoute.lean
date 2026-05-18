import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_l10_sibling_route [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n streamRead dyadicRead regseqRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w streamRead ->
        Cont streamRead q dyadicRead ->
          Cont dyadicRead q regseqRead ->
            Cont regseqRead e realRead ->
              PkgSig bundle realRead pkg ->
                UnaryHistory streamRead ∧ UnaryHistory dyadicRead ∧
                  UnaryHistory regseqRead ∧ UnaryHistory realRead ∧ Cont m0 m1 u ∧
                    Cont u v t ∧ Cont t w q ∧ Cont t w streamRead ∧
                      Cont streamRead q dyadicRead ∧ Cont dyadicRead q regseqRead ∧
                        Cont regseqRead e realRead ∧ PkgSig bundle p pkg ∧
                          PkgSig bundle realRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig hsame
  intro carrier streamRoute dyadicRoute regseqRoute realRoute realPkg
  obtain ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, wUnary, qUnary, eUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, m0m1u, uvt, twq, _qeh, pPkg, hn⟩ := carrier
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed tUnary wUnary streamRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed streamUnary qUnary dyadicRoute
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed dyadicUnary qUnary regseqRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regseqUnary eUnary realRoute
  exact
    ⟨streamUnary, dyadicUnary, regseqUnary, realUnary, m0m1u, uvt, twq, streamRoute,
      dyadicRoute, regseqRoute, realRoute, pPkg, realPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
