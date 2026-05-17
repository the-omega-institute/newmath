import BEDC.Derived.CauchyWitnessLedgerUp.TasteGate

namespace BEDC.Derived.CauchyWitnessLedgerUp

open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem CauchyWitnessLedgerForbidden_coordinate_exclusion
    {Q B S K H C P N extra : BHist} :
    FieldFaithful.fields (CauchyWitnessLedgerUp.mk Q B S K H C P N) =
        [Q, B, S, K, H, C, P, N] ∧
      FieldFaithful.fields (CauchyWitnessLedgerUp.mk Q B S K H C P N) ≠
        [Q, B, S, K, H, C, P, N, extra] := by
  -- BEDC touchpoint anchor: BHist FieldFaithful
  constructor
  · rfl
  · intro hfields
    injection hfields with _ tailQ
    injection tailQ with _ tailB
    injection tailB with _ tailS
    injection tailS with _ tailK
    injection tailK with _ tailH
    injection tailH with _ tailC
    injection tailC with _ tailP
    injection tailP
    contradiction

end BEDC.Derived.CauchyWitnessLedgerUp
