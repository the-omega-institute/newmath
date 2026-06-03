import BEDC.Derived.UniformCompletionFunctorUp.SourceFactorization

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCompletionFunctorExtensionOrdering [AskSetup] [PackageSetup]
    {U F E R W D S H C P N sourceHandoff extensionRead regseqRead windowRead dyadicRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionFunctorCarrier U F E R W D S H C P N bundle pkg ->
      Cont U F sourceHandoff ->
        Cont sourceHandoff E extensionRead ->
          Cont extensionRead R regseqRead ->
            Cont regseqRead W windowRead ->
              Cont windowRead D dyadicRead ->
                Cont dyadicRead S sealRead ->
                  PkgSig bundle sealRead pkg ->
                    Cont U (append F (append E (append R (append W (append D S)))))
                        sealRead ∧
                      UnaryHistory sourceHandoff ∧ UnaryHistory extensionRead ∧
                        UnaryHistory regseqRead ∧ UnaryHistory windowRead ∧
                          UnaryHistory dyadicRead ∧ UnaryHistory sealRead ∧
                            PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: UniformCompletionFunctorCarrier BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier sourceRoute extensionRoute regseqRoute windowRoute dyadicRoute sealRoute sealPkg
  obtain ⟨unaryU, unaryF, unaryE, unaryR, unaryW, unaryD, unaryS, _unaryH,
    _unaryC, _unaryP, _unaryN, _carrierSource, _carrierReadback, _carrierSeal,
    _provenancePkg, _namePkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceHandoff :=
    unary_cont_closed unaryU unaryF sourceRoute
  have extensionUnary : UnaryHistory extensionRead :=
    unary_cont_closed sourceUnary unaryE extensionRoute
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed extensionUnary unaryR regseqRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed regseqUnary unaryW windowRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed windowUnary unaryD dyadicRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicUnary unaryS sealRoute
  have orderedRoute :
      Cont U (append F (append E (append R (append W (append D S))))) sealRead := by
    cases sourceRoute
    cases extensionRoute
    cases regseqRoute
    cases windowRoute
    cases dyadicRoute
    cases sealRoute
    exact
      (append_assoc (append (append (append (append U F) E) R) W) D S).trans
        ((append_assoc (append (append (append U F) E) R) W (append D S)).trans
          ((append_assoc (append (append U F) E) R (append W (append D S))).trans
            ((append_assoc (append U F) E (append R (append W (append D S)))).trans
              (append_assoc U F (append E (append R (append W (append D S))))))))
  exact
    ⟨orderedRoute, sourceUnary, extensionUnary, regseqUnary, windowUnary, dyadicUnary,
      sealUnary, sealPkg⟩

end BEDC.Derived.UniformCompletionFunctorUp
