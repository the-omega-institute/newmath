import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopFanCompactUniformUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopFanCompactUniformUp : Type where
  | mk (K M B L U D H C P N : BHist) : BishopFanCompactUniformUp
  deriving DecidableEq

def bishopFanCompactUniformEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopFanCompactUniformEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopFanCompactUniformEncodeBHist h

def bishopFanCompactUniformDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopFanCompactUniformDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopFanCompactUniformDecodeBHist tail)

private theorem BishopFanCompactUniformTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      bishopFanCompactUniformDecodeBHist (bishopFanCompactUniformEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def bishopFanCompactUniformToEventFlow : BishopFanCompactUniformUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BishopFanCompactUniformUp.mk K M B L U D H C P N =>
      [bishopFanCompactUniformEncodeBHist K,
        bishopFanCompactUniformEncodeBHist M,
        bishopFanCompactUniformEncodeBHist B,
        bishopFanCompactUniformEncodeBHist L,
        bishopFanCompactUniformEncodeBHist U,
        bishopFanCompactUniformEncodeBHist D,
        bishopFanCompactUniformEncodeBHist H,
        bishopFanCompactUniformEncodeBHist C,
        bishopFanCompactUniformEncodeBHist P,
        bishopFanCompactUniformEncodeBHist N]

private def bishopFanCompactUniformEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopFanCompactUniformEventAtDefault index rest

def bishopFanCompactUniformFromEventFlow
    (ef : EventFlow) : Option BishopFanCompactUniformUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopFanCompactUniformUp.mk
      (bishopFanCompactUniformDecodeBHist (bishopFanCompactUniformEventAtDefault 0 ef))
      (bishopFanCompactUniformDecodeBHist (bishopFanCompactUniformEventAtDefault 1 ef))
      (bishopFanCompactUniformDecodeBHist (bishopFanCompactUniformEventAtDefault 2 ef))
      (bishopFanCompactUniformDecodeBHist (bishopFanCompactUniformEventAtDefault 3 ef))
      (bishopFanCompactUniformDecodeBHist (bishopFanCompactUniformEventAtDefault 4 ef))
      (bishopFanCompactUniformDecodeBHist (bishopFanCompactUniformEventAtDefault 5 ef))
      (bishopFanCompactUniformDecodeBHist (bishopFanCompactUniformEventAtDefault 6 ef))
      (bishopFanCompactUniformDecodeBHist (bishopFanCompactUniformEventAtDefault 7 ef))
      (bishopFanCompactUniformDecodeBHist (bishopFanCompactUniformEventAtDefault 8 ef))
      (bishopFanCompactUniformDecodeBHist (bishopFanCompactUniformEventAtDefault 9 ef)))

private theorem BishopFanCompactUniformTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopFanCompactUniformUp,
      bishopFanCompactUniformFromEventFlow (bishopFanCompactUniformToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K M B L U D H C P N =>
      change
        some
          (BishopFanCompactUniformUp.mk
            (bishopFanCompactUniformDecodeBHist (bishopFanCompactUniformEncodeBHist K))
            (bishopFanCompactUniformDecodeBHist (bishopFanCompactUniformEncodeBHist M))
            (bishopFanCompactUniformDecodeBHist (bishopFanCompactUniformEncodeBHist B))
            (bishopFanCompactUniformDecodeBHist (bishopFanCompactUniformEncodeBHist L))
            (bishopFanCompactUniformDecodeBHist (bishopFanCompactUniformEncodeBHist U))
            (bishopFanCompactUniformDecodeBHist (bishopFanCompactUniformEncodeBHist D))
            (bishopFanCompactUniformDecodeBHist (bishopFanCompactUniformEncodeBHist H))
            (bishopFanCompactUniformDecodeBHist (bishopFanCompactUniformEncodeBHist C))
            (bishopFanCompactUniformDecodeBHist (bishopFanCompactUniformEncodeBHist P))
            (bishopFanCompactUniformDecodeBHist (bishopFanCompactUniformEncodeBHist N))) =
          some (BishopFanCompactUniformUp.mk K M B L U D H C P N)
      rw [BishopFanCompactUniformTasteGate_single_carrier_alignment_decode_encode K,
        BishopFanCompactUniformTasteGate_single_carrier_alignment_decode_encode M,
        BishopFanCompactUniformTasteGate_single_carrier_alignment_decode_encode B,
        BishopFanCompactUniformTasteGate_single_carrier_alignment_decode_encode L,
        BishopFanCompactUniformTasteGate_single_carrier_alignment_decode_encode U,
        BishopFanCompactUniformTasteGate_single_carrier_alignment_decode_encode D,
        BishopFanCompactUniformTasteGate_single_carrier_alignment_decode_encode H,
        BishopFanCompactUniformTasteGate_single_carrier_alignment_decode_encode C,
        BishopFanCompactUniformTasteGate_single_carrier_alignment_decode_encode P,
        BishopFanCompactUniformTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopFanCompactUniformTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopFanCompactUniformUp} :
    bishopFanCompactUniformToEventFlow x = bishopFanCompactUniformToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopFanCompactUniformFromEventFlow (bishopFanCompactUniformToEventFlow x) =
        bishopFanCompactUniformFromEventFlow (bishopFanCompactUniformToEventFlow y) :=
    congrArg bishopFanCompactUniformFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopFanCompactUniformTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopFanCompactUniformTasteGate_single_carrier_alignment_round_trip y)))

instance bishopFanCompactUniformBHistCarrier : BHistCarrier BishopFanCompactUniformUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopFanCompactUniformToEventFlow
  fromEventFlow := bishopFanCompactUniformFromEventFlow

instance bishopFanCompactUniformChapterTasteGate :
    ChapterTasteGate BishopFanCompactUniformUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopFanCompactUniformFromEventFlow (bishopFanCompactUniformToEventFlow x) =
        some x
    exact BishopFanCompactUniformTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopFanCompactUniformTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate BishopFanCompactUniformUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopFanCompactUniformChapterTasteGate

theorem BishopFanCompactUniformTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier BishopFanCompactUniformUp) ∧
      Nonempty (ChapterTasteGate BishopFanCompactUniformUp) ∧
        (∀ x : BishopFanCompactUniformUp,
          BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
          bishopFanCompactUniformEncodeBHist BHist.Empty = ([] : List BMark) ∧
            bishopFanCompactUniformDecodeBHist [BMark.b0] = BHist.e0 BHist.Empty := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨bishopFanCompactUniformBHistCarrier⟩,
      ⟨bishopFanCompactUniformChapterTasteGate⟩,
      ChapterTasteGate.round_trip,
      rfl,
      rfl⟩

end BEDC.Derived.BishopFanCompactUniformUp.TasteGate
