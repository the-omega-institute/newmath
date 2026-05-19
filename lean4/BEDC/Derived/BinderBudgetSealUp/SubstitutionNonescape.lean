import BEDC.Derived.BinderBudgetSealUp.CarrierAdmission

namespace BEDC.Derived.BinderBudgetSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem BinderBudgetSealSubstitutionNonescape [AskSetup] [PackageSetup]
    {depth term payload shiftRoute substRoute transport contRoute provenance name substRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BinderBudgetSealCarrier depth term payload shiftRoute substRoute transport contRoute
        provenance name bundle pkg ->
      Cont substRoute name substRead ->
        PkgSig bundle substRead pkg ->
          UnaryHistory depth ∧ UnaryHistory term ∧ UnaryHistory payload ∧
            UnaryHistory substRoute ∧ UnaryHistory substRead ∧
              Cont depth payload substRoute ∧ Cont substRoute name substRead ∧
                PkgSig bundle name pkg ∧ PkgSig bundle substRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont UnaryHistory
  intro carrier substRouteNameRead substReadPkg
  obtain ⟨depthUnary, termUnary, payloadUnary, _shiftRouteUnary, substRouteUnary,
    _transportUnary, _contRouteUnary, _provenanceUnary, nameUnary, _depthTermShift,
    depthPayloadSubst, _shiftSubstCont, _provenancePkg, namePkg⟩ := carrier
  have substReadUnary : UnaryHistory substRead :=
    unary_cont_closed substRouteUnary nameUnary substRouteNameRead
  exact
    ⟨depthUnary, termUnary, payloadUnary, substRouteUnary, substReadUnary,
      depthPayloadSubst, substRouteNameRead, namePkg, substReadPkg⟩

end BEDC.Derived.BinderBudgetSealUp
