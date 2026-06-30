import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompleteOrderedFieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompleteOrderedFieldUp : Type where
  | mk : (O Q D E L T H C P N : BHist) → CompleteOrderedFieldUp
  deriving DecidableEq

def completeOrderedFieldEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completeOrderedFieldEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completeOrderedFieldEncodeBHist h

def completeOrderedFieldDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completeOrderedFieldDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completeOrderedFieldDecodeBHist tail)

private theorem completeOrderedFieldDecode_encode :
    ∀ h : BHist, completeOrderedFieldDecodeBHist (completeOrderedFieldEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def completeOrderedFieldFields : CompleteOrderedFieldUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompleteOrderedFieldUp.mk O Q D E L T H C P N =>
      [O, Q, D, E, L, T, H, C, P, N]

def completeOrderedFieldToEventFlow : CompleteOrderedFieldUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (completeOrderedFieldFields x).map completeOrderedFieldEncodeBHist

private def completeOrderedFieldEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => completeOrderedFieldEventAtDefault index rest

def completeOrderedFieldFromEventFlow (ef : EventFlow) :
    Option CompleteOrderedFieldUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompleteOrderedFieldUp.mk
      (completeOrderedFieldDecodeBHist (completeOrderedFieldEventAtDefault 0 ef))
      (completeOrderedFieldDecodeBHist (completeOrderedFieldEventAtDefault 1 ef))
      (completeOrderedFieldDecodeBHist (completeOrderedFieldEventAtDefault 2 ef))
      (completeOrderedFieldDecodeBHist (completeOrderedFieldEventAtDefault 3 ef))
      (completeOrderedFieldDecodeBHist (completeOrderedFieldEventAtDefault 4 ef))
      (completeOrderedFieldDecodeBHist (completeOrderedFieldEventAtDefault 5 ef))
      (completeOrderedFieldDecodeBHist (completeOrderedFieldEventAtDefault 6 ef))
      (completeOrderedFieldDecodeBHist (completeOrderedFieldEventAtDefault 7 ef))
      (completeOrderedFieldDecodeBHist (completeOrderedFieldEventAtDefault 8 ef))
      (completeOrderedFieldDecodeBHist (completeOrderedFieldEventAtDefault 9 ef)))

private theorem completeOrderedField_round_trip :
    ∀ x : CompleteOrderedFieldUp,
      completeOrderedFieldFromEventFlow (completeOrderedFieldToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O Q D E L T H C P N =>
      change
        some
          (CompleteOrderedFieldUp.mk
            (completeOrderedFieldDecodeBHist (completeOrderedFieldEncodeBHist O))
            (completeOrderedFieldDecodeBHist (completeOrderedFieldEncodeBHist Q))
            (completeOrderedFieldDecodeBHist (completeOrderedFieldEncodeBHist D))
            (completeOrderedFieldDecodeBHist (completeOrderedFieldEncodeBHist E))
            (completeOrderedFieldDecodeBHist (completeOrderedFieldEncodeBHist L))
            (completeOrderedFieldDecodeBHist (completeOrderedFieldEncodeBHist T))
            (completeOrderedFieldDecodeBHist (completeOrderedFieldEncodeBHist H))
            (completeOrderedFieldDecodeBHist (completeOrderedFieldEncodeBHist C))
            (completeOrderedFieldDecodeBHist (completeOrderedFieldEncodeBHist P))
            (completeOrderedFieldDecodeBHist (completeOrderedFieldEncodeBHist N))) =
          some (CompleteOrderedFieldUp.mk O Q D E L T H C P N)
      rw [completeOrderedFieldDecode_encode O, completeOrderedFieldDecode_encode Q,
        completeOrderedFieldDecode_encode D, completeOrderedFieldDecode_encode E,
        completeOrderedFieldDecode_encode L, completeOrderedFieldDecode_encode T,
        completeOrderedFieldDecode_encode H, completeOrderedFieldDecode_encode C,
        completeOrderedFieldDecode_encode P, completeOrderedFieldDecode_encode N]

private theorem completeOrderedFieldToEventFlow_injective
    {x y : CompleteOrderedFieldUp} :
    completeOrderedFieldToEventFlow x = completeOrderedFieldToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completeOrderedFieldFromEventFlow (completeOrderedFieldToEventFlow x) =
        completeOrderedFieldFromEventFlow (completeOrderedFieldToEventFlow y) :=
    congrArg completeOrderedFieldFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (completeOrderedField_round_trip x).symm
      (Eq.trans hread (completeOrderedField_round_trip y)))

instance completeOrderedFieldBHistCarrier : BHistCarrier CompleteOrderedFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completeOrderedFieldToEventFlow
  fromEventFlow := completeOrderedFieldFromEventFlow

instance completeOrderedFieldChapterTasteGate :
    ChapterTasteGate CompleteOrderedFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change completeOrderedFieldFromEventFlow (completeOrderedFieldToEventFlow x) = some x
    exact completeOrderedField_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (completeOrderedFieldToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CompleteOrderedFieldUp :=
  -- BEDC touchpoint anchor: BHist BMark
  completeOrderedFieldChapterTasteGate

theorem CompleteOrderedFieldTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CompleteOrderedFieldUp) ∧
      Nonempty (ChapterTasteGate CompleteOrderedFieldUp) ∧
      (∀ h : BHist, completeOrderedFieldDecodeBHist (completeOrderedFieldEncodeBHist h) = h) ∧
      (∀ x : CompleteOrderedFieldUp,
        completeOrderedFieldFromEventFlow (completeOrderedFieldToEventFlow x) = some x) ∧
      completeOrderedFieldEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨completeOrderedFieldBHistCarrier⟩, ⟨completeOrderedFieldChapterTasteGate⟩,
      completeOrderedFieldDecode_encode, completeOrderedField_round_trip, rfl⟩

end BEDC.Derived.CompleteOrderedFieldUp
