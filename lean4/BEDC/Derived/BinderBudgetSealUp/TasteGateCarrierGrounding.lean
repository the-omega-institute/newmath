import BEDC.Derived.BinderBudgetSealUp.CarrierAdmission

namespace BEDC.Derived.BinderBudgetSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem BinderBudgetSealTasteGateCarrierGrounding [AskSetup] [PackageSetup]
    {depth term payload shiftRoute substRoute transport contRoute provenance name gateRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BinderBudgetSealCarrier depth term payload shiftRoute substRoute transport contRoute
        provenance name bundle pkg ->
      Cont contRoute name gateRead ->
        PkgSig bundle gateRead pkg ->
          UnaryHistory depth ∧ UnaryHistory term ∧ UnaryHistory payload ∧
            UnaryHistory shiftRoute ∧ UnaryHistory substRoute ∧ UnaryHistory contRoute ∧
              UnaryHistory name ∧ UnaryHistory gateRead ∧ Cont depth term shiftRoute ∧
                Cont depth payload substRoute ∧ Cont contRoute name gateRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle gateRead pkg ∧
                    (forall x : BinderBudgetSealUp,
                      binderBudgetSealFromEventFlow (binderBudgetSealToEventFlow x) =
                        some x) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont UnaryHistory
  intro carrier contRouteNameGate gateReadPkg
  obtain ⟨depthUnary, termUnary, payloadUnary, shiftRouteUnary, substRouteUnary,
    _transportUnary, contRouteUnary, _provenanceUnary, nameUnary, depthTermShift,
    depthPayloadSubst, _shiftSubstCont, provenancePkg, _namePkg⟩ := carrier
  have gateReadUnary : UnaryHistory gateRead :=
    unary_cont_closed contRouteUnary nameUnary contRouteNameGate
  have roundTrip :
      forall x : BinderBudgetSealUp,
        binderBudgetSealFromEventFlow (binderBudgetSealToEventFlow x) = some x :=
    BinderBudgetSealTasteGate_single_carrier_alignment.left
  exact
    ⟨depthUnary, termUnary, payloadUnary, shiftRouteUnary, substRouteUnary, contRouteUnary,
      nameUnary, gateReadUnary, depthTermShift, depthPayloadSubst, contRouteNameGate,
      provenancePkg, gateReadPkg, roundTrip⟩

end BEDC.Derived.BinderBudgetSealUp
