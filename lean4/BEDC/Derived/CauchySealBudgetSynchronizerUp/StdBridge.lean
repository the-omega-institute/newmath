import BEDC.Derived.CauchySealBudgetSynchronizerUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchySealBudgetSynchronizerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchySealBudgetSynchronizerUp_StdBridge [AskSetup] [PackageSetup]
    {request sealRow budget tail selector compatibility transport route provenance nameCert
      endpoint bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    cauchySealBudgetSynchronizerFields
        (CauchySealBudgetSynchronizerUp.mk request sealRow budget tail selector
          compatibility transport route provenance nameCert) =
        [request, sealRow, budget, tail, selector, compatibility, transport, route,
          provenance, nameCert] →
      UnaryHistory endpoint →
        UnaryHistory route →
          Cont endpoint route bridgeRead →
            PkgSig bundle endpoint pkg →
              PkgSig bundle bridgeRead pkg →
                UnaryHistory bridgeRead ∧ hsame endpoint endpoint ∧
                  Cont endpoint route bridgeRead ∧ PkgSig bundle endpoint pkg ∧
                    PkgSig bundle bridgeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame PkgSig
  intro _fields endpointUnary routeUnary endpointRouteBridge endpointPkg bridgePkg
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed endpointUnary routeUnary endpointRouteBridge
  exact
    ⟨bridgeUnary, hsame_refl endpoint, endpointRouteBridge, endpointPkg, bridgePkg⟩

end BEDC.Derived.CauchySealBudgetSynchronizerUp
