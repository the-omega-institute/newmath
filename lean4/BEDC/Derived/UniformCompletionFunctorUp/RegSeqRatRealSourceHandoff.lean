import BEDC.Derived.UniformCompletionFunctorUp.SourceFactorization

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCompletionFunctorRegSeqRatRealSourceHandoff [AskSetup] [PackageSetup]
    {U F E R W D S H C P N regseqRead windowRead dyadicRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionFunctorCarrier U F E R W D S H C P N bundle pkg ->
      Cont E R regseqRead ->
        Cont regseqRead W windowRead ->
          Cont windowRead D dyadicRead ->
            Cont dyadicRead S sealRead ->
              PkgSig bundle sealRead pkg ->
                UnaryHistory regseqRead ∧ UnaryHistory windowRead ∧
                  UnaryHistory dyadicRead ∧ UnaryHistory sealRead ∧
                    Cont E R regseqRead ∧ Cont regseqRead W windowRead ∧
                      Cont windowRead D dyadicRead ∧ Cont dyadicRead S sealRead ∧
                        PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier regseqRoute windowRoute dyadicRoute sealRoute sealPkg
  obtain ⟨_uUnary, _fUnary, eUnary, rUnary, wUnary, dUnary, sUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _sourceRoute, _readbackRoute, _sealCarrierRoute,
      _sourcePkg, _namePkg⟩ := carrier
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed eUnary rUnary regseqRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed regseqUnary wUnary windowRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed windowUnary dUnary dyadicRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicUnary sUnary sealRoute
  exact
    ⟨regseqUnary, windowUnary, dyadicUnary, sealUnary, regseqRoute, windowRoute,
      dyadicRoute, sealRoute, sealPkg⟩

end BEDC.Derived.UniformCompletionFunctorUp
