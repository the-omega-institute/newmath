import BEDC.Derived.UniformCompletionFunctorUp.SourceFactorization

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCompletionFunctorCarrier_dyadic_window_stability [AskSetup] [PackageSetup]
    {U F E R W D S H C P N readbackRead dyadicRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionFunctorCarrier U F E R W D S H C P N bundle pkg ->
      Cont R W readbackRead ->
        Cont W D dyadicRead ->
          Cont dyadicRead S sealRead ->
            PkgSig bundle sealRead pkg ->
              UnaryHistory readbackRead ∧ UnaryHistory dyadicRead ∧ hsame S dyadicRead ∧
                Cont R W readbackRead ∧ Cont W D dyadicRead ∧
                  Cont dyadicRead S sealRead ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: UniformCompletionFunctorCarrier BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier readbackRoute dyadicRoute sealRoute sealPkg
  obtain ⟨_unaryU, _unaryF, _unaryE, unaryR, unaryW, unaryD, _unaryS, _unaryH,
    _unaryC, _unaryP, _unaryN, _sourceRoute, _readbackRoute, carrierDyadicRoute,
      _pkgP, _pkgN⟩ := carrier
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed unaryR unaryW readbackRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed unaryW unaryD dyadicRoute
  have sameDyadic : hsame S dyadicRead :=
    cont_respects_hsame (hsame_refl W) (hsame_refl D) carrierDyadicRoute dyadicRoute
  exact
    ⟨readbackUnary, dyadicUnary, sameDyadic, readbackRoute, dyadicRoute, sealRoute, sealPkg⟩

end BEDC.Derived.UniformCompletionFunctorUp
