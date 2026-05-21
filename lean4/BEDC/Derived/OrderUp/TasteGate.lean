import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OrderUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OrderUp : Type where
  | mk
      (left right branchLedger endpointClassifier transportReplay contReplay provenance :
        BHist) :
        OrderUp
  deriving DecidableEq

def orderUpEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: orderUpEncodeBHist h
  | BHist.e1 h => BMark.b1 :: orderUpEncodeBHist h

def orderUpDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (orderUpDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (orderUpDecodeBHist tail)

private theorem orderUpDecode_encode_bhist :
    ∀ h : BHist, orderUpDecodeBHist (orderUpEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def orderUpFields : OrderUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OrderUp.mk left right branchLedger endpointClassifier transportReplay contReplay
      provenance =>
      [left, right, branchLedger, endpointClassifier, transportReplay, contReplay, provenance]

def orderUpToEventFlow : OrderUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | OrderUp.mk left right branchLedger endpointClassifier transportReplay contReplay
      provenance =>
      [[BMark.b1, BMark.b0, BMark.b1],
        orderUpEncodeBHist left,
        orderUpEncodeBHist right,
        orderUpEncodeBHist branchLedger,
        orderUpEncodeBHist endpointClassifier,
        orderUpEncodeBHist transportReplay,
        orderUpEncodeBHist contReplay,
        orderUpEncodeBHist provenance]

private def orderUpEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => orderUpEventAt index rest

def orderUpFromEventFlow : EventFlow → Option OrderUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (OrderUp.mk
          (orderUpDecodeBHist (orderUpEventAt 1 ef))
          (orderUpDecodeBHist (orderUpEventAt 2 ef))
          (orderUpDecodeBHist (orderUpEventAt 3 ef))
          (orderUpDecodeBHist (orderUpEventAt 4 ef))
          (orderUpDecodeBHist (orderUpEventAt 5 ef))
          (orderUpDecodeBHist (orderUpEventAt 6 ef))
          (orderUpDecodeBHist (orderUpEventAt 7 ef)))

private theorem orderUp_round_trip :
    ∀ x : OrderUp, orderUpFromEventFlow (orderUpToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk left right branchLedger endpointClassifier transportReplay contReplay provenance =>
      change
        some
          (OrderUp.mk
            (orderUpDecodeBHist (orderUpEncodeBHist left))
            (orderUpDecodeBHist (orderUpEncodeBHist right))
            (orderUpDecodeBHist (orderUpEncodeBHist branchLedger))
            (orderUpDecodeBHist (orderUpEncodeBHist endpointClassifier))
            (orderUpDecodeBHist (orderUpEncodeBHist transportReplay))
            (orderUpDecodeBHist (orderUpEncodeBHist contReplay))
            (orderUpDecodeBHist (orderUpEncodeBHist provenance))) =
          some
            (OrderUp.mk left right branchLedger endpointClassifier transportReplay contReplay
              provenance)
      rw [orderUpDecode_encode_bhist left, orderUpDecode_encode_bhist right,
        orderUpDecode_encode_bhist branchLedger,
        orderUpDecode_encode_bhist endpointClassifier,
        orderUpDecode_encode_bhist transportReplay, orderUpDecode_encode_bhist contReplay,
        orderUpDecode_encode_bhist provenance]

private theorem orderUpToEventFlow_injective {x y : OrderUp} :
    orderUpToEventFlow x = orderUpToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      orderUpFromEventFlow (orderUpToEventFlow x) =
        orderUpFromEventFlow (orderUpToEventFlow y) :=
    congrArg orderUpFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (orderUp_round_trip x).symm (Eq.trans hread (orderUp_round_trip y)))

private theorem orderUp_fields_faithful :
    ∀ x y : OrderUp, orderUpFields x = orderUpFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk left₁ right₁ branchLedger₁ endpointClassifier₁ transportReplay₁ contReplay₁
      provenance₁ =>
      cases y with
      | mk left₂ right₂ branchLedger₂ endpointClassifier₂ transportReplay₂ contReplay₂
          provenance₂ =>
          injection h with hleft rest₁
          injection rest₁ with hright rest₂
          injection rest₂ with hbranchLedger rest₃
          injection rest₃ with hendpointClassifier rest₄
          injection rest₄ with htransportReplay rest₅
          injection rest₅ with hcontReplay rest₆
          injection rest₆ with hprovenance _
          cases hleft
          cases hright
          cases hbranchLedger
          cases hendpointClassifier
          cases htransportReplay
          cases hcontReplay
          cases hprovenance
          rfl

instance orderUpBHistCarrier : BHistCarrier OrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := orderUpToEventFlow
  fromEventFlow := orderUpFromEventFlow

instance orderUpChapterTasteGate : ChapterTasteGate OrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change orderUpFromEventFlow (orderUpToEventFlow x) = some x
    exact orderUp_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (orderUpToEventFlow_injective heq)

instance orderUpFieldFaithful : FieldFaithful OrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := orderUpFields
  field_faithful := orderUp_fields_faithful

instance orderUpNontrivial : Nontrivial OrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨OrderUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      OrderUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem OrderUpTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate OrderUp) ∧
      Nonempty (FieldFaithful OrderUp) ∧
        Nonempty (Nontrivial OrderUp) ∧
          (∀ h : BHist, orderUpDecodeBHist (orderUpEncodeBHist h) = h) ∧
            (∀ x : OrderUp, orderUpFromEventFlow (orderUpToEventFlow x) = some x) ∧
              (∀ x y : OrderUp, orderUpToEventFlow x = orderUpToEventFlow y → x = y) ∧
                orderUpEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨Nonempty.intro orderUpChapterTasteGate,
      Nonempty.intro orderUpFieldFaithful,
      Nonempty.intro orderUpNontrivial,
      orderUpDecode_encode_bhist,
      orderUp_round_trip,
      by
        intro x y heq
        exact orderUpToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.OrderUp.TasteGate
