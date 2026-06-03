import BEDC.Derived.UniformCompletionFunctorUp.SourceFactorization

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCompletionFunctorSourceUnitCompatibility [AskSetup] [PackageSetup]
    {U F E R W D S H C P N sourceRead extensionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionFunctorCarrier U F E R W D S H C P N bundle pkg ->
      Cont U F sourceRead ->
        Cont sourceRead E extensionRead ->
          UnaryHistory U ∧ UnaryHistory F ∧ UnaryHistory sourceRead ∧
            UnaryHistory extensionRead ∧ Cont U F sourceRead ∧
              Cont sourceRead E extensionRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: UniformCompletionFunctorCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceRoute extensionRoute
  obtain ⟨unaryU, unaryF, unaryE, _unaryR, _unaryW, _unaryD, _unaryS, _unaryH,
    _unaryC, _unaryP, _unaryN, _carrierSourceRoute, _carrierReadbackRoute,
      _carrierSealRoute, provenancePkg, localNamePkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryU unaryF sourceRoute
  have extensionUnary : UnaryHistory extensionRead :=
    unary_cont_closed sourceUnary unaryE extensionRoute
  exact
    ⟨unaryU, unaryF, sourceUnary, extensionUnary, sourceRoute, extensionRoute,
      provenancePkg, localNamePkg⟩

end BEDC.Derived.UniformCompletionFunctorUp
