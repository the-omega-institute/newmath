import BEDC.Derived.SocketUseLedgerUp.TasteGate

namespace BEDC.Derived.SocketUseLedgerUp

open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem SocketUseLedgerCarrier_visible_refusal_layer_separation :
    (∀ x : SocketUseLedgerUp,
      ∃ A S Q V R H C P N : BHist,
        x = SocketUseLedgerUp.mk A S Q V R H C P N ∧
          FieldFaithful.fields x = [A, S, Q, V, R, H, C, P, N]) ∧
      (∀ A S Q H C P N : BHist,
        BHistCarrier.toEventFlow
          (SocketUseLedgerUp.mk A S Q (BHist.e0 BHist.Empty) BHist.Empty H C P N) ≠
        BHistCarrier.toEventFlow
          (SocketUseLedgerUp.mk A S Q BHist.Empty (BHist.e0 BHist.Empty) H C P N)) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    cases x with
    | mk A S Q V R H C P N =>
        exact ⟨A, S, Q, V, R, H, C, P, N, rfl, rfl⟩
  · intro A S Q H C P N heq
    change
      socketUseLedgerToEventFlow
          (SocketUseLedgerUp.mk A S Q (BHist.e0 BHist.Empty) BHist.Empty H C P N) =
        socketUseLedgerToEventFlow
          (SocketUseLedgerUp.mk A S Q BHist.Empty (BHist.e0 BHist.Empty) H C P N) at heq
    injection heq with _ htail₁
    injection htail₁ with _ htail₂
    injection htail₂ with _ htail₃
    injection htail₃ with hrow _
    cases hrow

end BEDC.Derived.SocketUseLedgerUp
