import BEDC.Derived.UniformCompletionFunctorUp.BridgeTargetInterface

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCompletionFunctorTargetSourceOrder [AskSetup] [PackageSetup]
    {U F E R W D S H C P N sourceRead extensionRead readbackRead windowRead dyadicRead
      sealRead targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionFunctorCarrier U F E R W D S H C P N bundle pkg ->
      Cont U F sourceRead ->
        Cont sourceRead E extensionRead ->
          Cont extensionRead R readbackRead ->
            Cont extensionRead W windowRead ->
              Cont windowRead D dyadicRead ->
                Cont dyadicRead S sealRead ->
                  Cont sealRead H targetRead ->
                    PkgSig bundle sealRead pkg ->
                      UnaryHistory U ∧ UnaryHistory F ∧ UnaryHistory E ∧
                        UnaryHistory R ∧ UnaryHistory W ∧ UnaryHistory D ∧
                          UnaryHistory S ∧ UnaryHistory sourceRead ∧
                            UnaryHistory extensionRead ∧ UnaryHistory readbackRead ∧
                              UnaryHistory windowRead ∧ UnaryHistory dyadicRead ∧
                                UnaryHistory sealRead ∧ UnaryHistory targetRead ∧
                                  Cont U F sourceRead ∧
                                    Cont sourceRead E extensionRead ∧
                                      Cont extensionRead R readbackRead ∧
                                        Cont extensionRead W windowRead ∧
                                          Cont windowRead D dyadicRead ∧
                                            Cont dyadicRead S sealRead ∧
                                              Cont sealRead H targetRead ∧
                                                PkgSig bundle P pkg ∧
                                                  PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: UniformCompletionFunctorCarrier BHist ProbeBundle PkgSig Cont UnaryHistory
  intro carrier sourceRoute extensionRoute readbackRoute windowRoute dyadicRoute sealRoute
    targetRoute sealPkg
  obtain ⟨unaryU, unaryF, unaryE, unaryR, unaryW, unaryD, unaryS, unaryH,
    _unaryC, _unaryP, _unaryN, _carrierSourceRoute, _carrierReadbackRoute,
      _carrierSealRoute, provenancePkg, _localNamePkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryU unaryF sourceRoute
  have extensionUnary : UnaryHistory extensionRead :=
    unary_cont_closed sourceUnary unaryE extensionRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed extensionUnary unaryR readbackRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed extensionUnary unaryW windowRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed windowUnary unaryD dyadicRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicUnary unaryS sealRoute
  have targetUnary : UnaryHistory targetRead :=
    unary_cont_closed sealUnary unaryH targetRoute
  exact
    ⟨unaryU, unaryF, unaryE, unaryR, unaryW, unaryD, unaryS, sourceUnary,
      extensionUnary, readbackUnary, windowUnary, dyadicUnary, sealUnary, targetUnary,
      sourceRoute, extensionRoute, readbackRoute, windowRoute, dyadicRoute, sealRoute,
      targetRoute, provenancePkg, sealPkg⟩

end BEDC.Derived.UniformCompletionFunctorUp
