import BEDC.Derived.UniformCompletionFunctorUp.SourceFactorization

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCompletionFunctorSourceExtensionReadback [AskSetup] [PackageSetup]
    {U F E R W D S H C P N sourceRead extensionRead regseqRead windowRead
      dyadicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionFunctorCarrier U F E R W D S H C P N bundle pkg →
      Cont U F sourceRead →
        Cont sourceRead E extensionRead →
          Cont extensionRead R regseqRead →
            Cont regseqRead W windowRead →
              Cont windowRead D dyadicRead →
                PkgSig bundle N pkg →
                  UnaryHistory sourceRead ∧ UnaryHistory extensionRead ∧
                    UnaryHistory regseqRead ∧ UnaryHistory windowRead ∧
                      UnaryHistory dyadicRead ∧ Cont U F sourceRead ∧
                        Cont sourceRead E extensionRead ∧
                          Cont extensionRead R regseqRead ∧
                            Cont regseqRead W windowRead ∧ Cont windowRead D dyadicRead ∧
                              PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: UniformCompletionFunctorCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceRoute extensionRoute regseqRoute windowRoute dyadicRoute localNamePkg
  obtain ⟨unaryU, unaryF, unaryE, unaryR, unaryW, unaryD, _unaryS, _unaryH,
    _unaryC, _unaryP, _unaryN, _carrierSourceRoute, _carrierReadbackRoute,
      _carrierSealRoute, _provenancePkg, _carrierNamePkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryU unaryF sourceRoute
  have extensionUnary : UnaryHistory extensionRead :=
    unary_cont_closed sourceUnary unaryE extensionRoute
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed extensionUnary unaryR regseqRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed regseqUnary unaryW windowRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed windowUnary unaryD dyadicRoute
  exact
    ⟨sourceUnary, extensionUnary, regseqUnary, windowUnary, dyadicUnary, sourceRoute,
      extensionRoute, regseqRoute, windowRoute, dyadicRoute, localNamePkg⟩

end BEDC.Derived.UniformCompletionFunctorUp
