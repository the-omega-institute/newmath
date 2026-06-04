import BEDC.Derived.UniformCompletionFunctorUp.RouteObligations

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCompletionFunctorRootObligationSurface [AskSetup] [PackageSetup]
    {U F E R W D S H C P N sourceRead extensionRead readbackRead windowRead dyadicRead
      sealRead transported replayed sourced named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionFunctorCarrier U F E R W D S H C P N bundle pkg →
      Cont U F sourceRead →
        Cont sourceRead E extensionRead →
          Cont extensionRead R readbackRead →
            Cont extensionRead W windowRead →
              Cont windowRead D dyadicRead →
                Cont dyadicRead S sealRead →
                  Cont sealRead H transported →
                    Cont transported C replayed →
                      Cont replayed P sourced →
                        Cont sourced N named →
                          PkgSig bundle named pkg →
                            UnaryHistory sourceRead ∧ UnaryHistory extensionRead ∧
                              UnaryHistory readbackRead ∧ UnaryHistory windowRead ∧
                                UnaryHistory dyadicRead ∧ UnaryHistory sealRead ∧
                                  UnaryHistory transported ∧ UnaryHistory replayed ∧
                                    UnaryHistory sourced ∧ UnaryHistory named ∧
                                      PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                                        PkgSig bundle named pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier sourceRoute extensionRoute readbackRoute windowRoute dyadicRoute sealRoute
    transportRoute replayRoute sourcePkgRoute namedRoute namedPkg
  obtain ⟨unaryU, unaryF, unaryE, unaryR, unaryW, unaryD, unaryS, unaryH,
    unaryC, unaryP, unaryN, _carrierSourceRoute, _carrierReadbackRoute,
      _carrierSealRoute, provenancePkg, localNamePkg⟩ := carrier
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
  have transportedUnary : UnaryHistory transported :=
    unary_cont_closed sealUnary unaryH transportRoute
  have replayedUnary : UnaryHistory replayed :=
    unary_cont_closed transportedUnary unaryC replayRoute
  have sourcedUnary : UnaryHistory sourced :=
    unary_cont_closed replayedUnary unaryP sourcePkgRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed sourcedUnary unaryN namedRoute
  exact
    ⟨sourceUnary, extensionUnary, readbackUnary, windowUnary, dyadicUnary, sealUnary,
      transportedUnary, replayedUnary, sourcedUnary, namedUnary, provenancePkg,
      localNamePkg, namedPkg⟩

end BEDC.Derived.UniformCompletionFunctorUp
