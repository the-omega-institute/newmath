import BEDC.Derived.AxisCarryRefusalLedgerUp.TasteGate

namespace BEDC.Derived.AxisCarryRefusalLedgerUp

open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem AxisCarryRefusalLedgerCarrier_negative_row_layer_separation :
    (∀ x : AxisCarryRefusalLedgerUp,
      ∃ G Z F A B L H C P N : BHist,
        x = AxisCarryRefusalLedgerUp.mk G Z F A B L H C P N ∧
          FieldFaithful.fields x = [G, Z, F, A, B, L, H, C, P, N]) ∧
      (∀ G F A B L H C P N : BHist,
        BHistCarrier.toEventFlow
          (AxisCarryRefusalLedgerUp.mk G (BHist.e0 BHist.Empty) F A B L H C P N) ≠
        BHistCarrier.toEventFlow
          (AxisCarryRefusalLedgerUp.mk G BHist.Empty F A B L H C P N)) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    cases x with
    | mk G Z F A B L H C P N =>
        exact ⟨G, Z, F, A, B, L, H, C, P, N, rfl, rfl⟩
  · intro G F A B L H C P N heq
    change
      axisCarryRefusalLedgerToEventFlow
          (AxisCarryRefusalLedgerUp.mk G (BHist.e0 BHist.Empty) F A B L H C P N) =
        axisCarryRefusalLedgerToEventFlow
          (AxisCarryRefusalLedgerUp.mk G BHist.Empty F A B L H C P N) at heq
    injection heq with _ htail₁
    injection htail₁ with _ htail₂
    injection htail₂ with _ htail₃
    injection htail₃ with hrow _
    cases hrow

theorem AxisCarryRefusalLedgerCarrier_bridge_boundary_preservation :
    (∀ x : AxisCarryRefusalLedgerUp,
      ∃ G Z F A B L H C P N : BHist,
        x = AxisCarryRefusalLedgerUp.mk G Z F A B L H C P N ∧
          FieldFaithful.fields x = [G, Z, F, A, B, L, H, C, P, N]) ∧
      (∀ G Z F A L H C P N : BHist,
        BHistCarrier.toEventFlow
          (AxisCarryRefusalLedgerUp.mk G Z F A (BHist.e0 BHist.Empty) L H C P N) ≠
        BHistCarrier.toEventFlow
          (AxisCarryRefusalLedgerUp.mk G Z F A BHist.Empty L H C P N)) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    cases x with
    | mk G Z F A B L H C P N =>
        exact ⟨G, Z, F, A, B, L, H, C, P, N, rfl, rfl⟩
  · intro G Z F A L H C P N heq
    change
      axisCarryRefusalLedgerToEventFlow
          (AxisCarryRefusalLedgerUp.mk G Z F A (BHist.e0 BHist.Empty) L H C P N) =
        axisCarryRefusalLedgerToEventFlow
          (AxisCarryRefusalLedgerUp.mk G Z F A BHist.Empty L H C P N) at heq
    injection heq with _ htail₁
    injection htail₁ with _ htail₂
    injection htail₂ with _ htail₃
    injection htail₃ with _ htail₄
    injection htail₄ with _ htail₅
    injection htail₅ with _ htail₆
    injection htail₆ with _ htail₇
    injection htail₇ with _ htail₈
    injection htail₈ with _ htail₉
    injection htail₉ with hrow _
    cases hrow

end BEDC.Derived.AxisCarryRefusalLedgerUp
