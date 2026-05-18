import BEDC.Derived.BinderBudgetSealUp.CarrierAdmission

namespace BEDC.Derived.BinderBudgetSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BinderBudgetSealSelfCompileHandoff [AskSetup] [PackageSetup]
    {depth term payload shiftRoute substRoute transport contRoute provenance name shiftRead
      substRead handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BinderBudgetSealCarrier depth term payload shiftRoute substRoute transport contRoute
        provenance name bundle pkg ->
      Cont shiftRoute name shiftRead ->
        Cont substRoute name substRead ->
          Cont shiftRead substRead handoff ->
            PkgSig bundle shiftRead pkg ->
              PkgSig bundle substRead pkg ->
                PkgSig bundle handoff pkg ->
                  UnaryHistory depth ∧ UnaryHistory term ∧ UnaryHistory payload ∧
                    UnaryHistory shiftRoute ∧ UnaryHistory substRoute ∧
                      UnaryHistory shiftRead ∧ UnaryHistory substRead ∧
                        UnaryHistory handoff ∧ Cont depth term shiftRoute ∧
                          Cont depth payload substRoute ∧ Cont shiftRoute name shiftRead ∧
                            Cont substRoute name substRead ∧ Cont shiftRead substRead handoff ∧
                              PkgSig bundle name pkg ∧ PkgSig bundle shiftRead pkg ∧
                                PkgSig bundle substRead pkg ∧ PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier shiftRouteNameRead substRouteNameRead shiftSubstHandoff shiftReadPkg
    substReadPkg handoffPkg
  obtain ⟨depthUnary, termUnary, payloadUnary, shiftRouteUnary, substRouteUnary,
    _transportUnary, _contRouteUnary, _provenanceUnary, nameUnary, depthTermShift,
    depthPayloadSubst, _shiftSubstCont, namePkg⟩ := carrier
  have shiftReadUnary : UnaryHistory shiftRead :=
    unary_cont_closed shiftRouteUnary nameUnary shiftRouteNameRead
  have substReadUnary : UnaryHistory substRead :=
    unary_cont_closed substRouteUnary nameUnary substRouteNameRead
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed shiftReadUnary substReadUnary shiftSubstHandoff
  exact
    ⟨depthUnary, termUnary, payloadUnary, shiftRouteUnary, substRouteUnary, shiftReadUnary,
      substReadUnary, handoffUnary, depthTermShift, depthPayloadSubst, shiftRouteNameRead,
      substRouteNameRead, shiftSubstHandoff, namePkg, shiftReadPkg, substReadPkg,
      handoffPkg⟩

end BEDC.Derived.BinderBudgetSealUp
