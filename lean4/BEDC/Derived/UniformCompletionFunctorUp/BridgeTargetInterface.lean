import BEDC.Derived.UniformCompletionFunctorUp.BridgeSourceLock

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCompletionFunctorBridgeTargetInterface [AskSetup] [PackageSetup]
    {U F E R W D S H C P N sourceRead extensionRead readbackRead windowRead dyadicRead
      sealRead targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionFunctorCarrier U F E R W D S H C P N bundle pkg →
      Cont U F sourceRead →
        Cont sourceRead E extensionRead →
          Cont extensionRead R readbackRead →
            Cont extensionRead W windowRead →
              Cont windowRead D dyadicRead →
                Cont dyadicRead S sealRead →
                  Cont sealRead H targetRead →
                    PkgSig bundle sealRead pkg →
                      UnaryHistory targetRead ∧ Cont sealRead H targetRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: UniformCompletionFunctorCarrier BHist ProbeBundle PkgSig Cont UnaryHistory
  intro carrier sourceRoute extensionRoute readbackRoute windowRoute dyadicRoute sealRoute
    targetRoute sealPkg
  obtain ⟨unaryU, unaryF, unaryE, _unaryR, unaryW, unaryD, unaryS, unaryH,
    _unaryC, _unaryP, _unaryN, _carrierSourceRoute, _carrierReadbackRoute,
      _carrierSealRoute, provenancePkg, _localNamePkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryU unaryF sourceRoute
  have extensionReadUnary : UnaryHistory extensionRead :=
    unary_cont_closed sourceReadUnary unaryE extensionRoute
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed extensionReadUnary unaryW windowRoute
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed windowReadUnary unaryD dyadicRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicReadUnary unaryS sealRoute
  have targetUnary : UnaryHistory targetRead :=
    unary_cont_closed sealReadUnary unaryH targetRoute
  exact ⟨targetUnary, targetRoute, provenancePkg, sealPkg⟩

end BEDC.Derived.UniformCompletionFunctorUp
