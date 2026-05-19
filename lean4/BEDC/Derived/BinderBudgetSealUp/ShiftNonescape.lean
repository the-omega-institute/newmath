import BEDC.Derived.BinderBudgetSealUp.CarrierAdmission

namespace BEDC.Derived.BinderBudgetSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem BinderBudgetSealShiftNonescape [AskSetup] [PackageSetup]
    {depth term payload shiftRoute substRoute transport contRoute provenance name shiftRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BinderBudgetSealCarrier depth term payload shiftRoute substRoute transport contRoute
        provenance name bundle pkg ->
      Cont shiftRoute name shiftRead ->
        PkgSig bundle shiftRead pkg ->
          UnaryHistory depth ∧ UnaryHistory term ∧ UnaryHistory shiftRoute ∧
            UnaryHistory shiftRead ∧ Cont depth term shiftRoute ∧
              Cont shiftRoute name shiftRead ∧ PkgSig bundle name pkg ∧
                PkgSig bundle shiftRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont UnaryHistory
  intro carrier shiftRouteNameRead shiftReadPkg
  obtain ⟨depthUnary, termUnary, _payloadUnary, shiftRouteUnary, _substRouteUnary,
    _transportUnary, _contRouteUnary, _provenanceUnary, nameUnary, depthTermShift,
    _depthPayloadSubst, _shiftSubstCont, _provenancePkg, namePkg⟩ := carrier
  have shiftReadUnary : UnaryHistory shiftRead :=
    unary_cont_closed shiftRouteUnary nameUnary shiftRouteNameRead
  exact
    ⟨depthUnary, termUnary, shiftRouteUnary, shiftReadUnary, depthTermShift,
      shiftRouteNameRead, namePkg, shiftReadPkg⟩

end BEDC.Derived.BinderBudgetSealUp
