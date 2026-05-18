import BEDC.Derived.BinderBudgetSealUp.CarrierAdmission

namespace BEDC.Derived.BinderBudgetSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem BinderBudgetSealCompilerBoundary [AskSetup] [PackageSetup]
    {depth term payload shiftRoute substRoute transport contRoute provenance name shiftRead
      substRead compilerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BinderBudgetSealCarrier depth term payload shiftRoute substRoute transport contRoute
        provenance name bundle pkg ->
      Cont shiftRoute name shiftRead ->
        Cont substRoute name substRead ->
          Cont shiftRead substRead compilerRead ->
            PkgSig bundle compilerRead pkg ->
              UnaryHistory depth ∧ UnaryHistory term ∧ UnaryHistory payload ∧
                UnaryHistory shiftRead ∧ UnaryHistory substRead ∧
                  UnaryHistory compilerRead ∧ Cont depth term shiftRoute ∧
                    Cont depth payload substRoute ∧ Cont shiftRead substRead compilerRead ∧
                      PkgSig bundle name pkg ∧ PkgSig bundle compilerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier shiftRouteNameRead substRouteNameRead shiftSubstCompiler compilerPkg
  obtain ⟨depthUnary, termUnary, payloadUnary, shiftRouteUnary, substRouteUnary,
    _transportUnary, _contRouteUnary, _provenanceUnary, nameUnary, depthTermShift,
    depthPayloadSubst, _shiftSubstCont, namePkg⟩ := carrier
  have shiftReadUnary : UnaryHistory shiftRead :=
    unary_cont_closed shiftRouteUnary nameUnary shiftRouteNameRead
  have substReadUnary : UnaryHistory substRead :=
    unary_cont_closed substRouteUnary nameUnary substRouteNameRead
  have compilerReadUnary : UnaryHistory compilerRead :=
    unary_cont_closed shiftReadUnary substReadUnary shiftSubstCompiler
  exact
    ⟨depthUnary, termUnary, payloadUnary, shiftReadUnary, substReadUnary,
      compilerReadUnary, depthTermShift, depthPayloadSubst, shiftSubstCompiler, namePkg,
      compilerPkg⟩

end BEDC.Derived.BinderBudgetSealUp
