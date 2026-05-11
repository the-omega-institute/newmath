import BEDC.Derived.S1Up

namespace BEDC.Derived.S1Up

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem SOneComponentClassifier_standard_bridge_transport
    {x y e p x' y' e' p' bridge ledger ledger' : BHist} :
    SOneComponentClassifier x y e p x' y' e' p' -> Cont p bridge ledger ->
      Cont p' bridge ledger' ->
        SOneLedgerPolicy x y e p x' y' e' p' ∧ hsame ledger ledger' := by
  intro classifier sourceBridge targetBridge
  have ledgerPolicy : SOneLedgerPolicy x y e p x' y' e' p' :=
    SOneLedgerPolicy_component_readback classifier
  have samePoint : hsame p p' := ledgerPolicy.right.right.left
  have sameBridge : hsame ledger ledger' :=
    cont_respects_hsame samePoint (hsame_refl bridge) sourceBridge targetBridge
  exact And.intro ledgerPolicy sameBridge

end BEDC.Derived.S1Up
