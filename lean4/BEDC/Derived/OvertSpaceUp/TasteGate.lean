import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OvertSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OvertSpaceUp : Type where
  | mk
      (space basis positivity witness locatedReal compactHandoff transport replay provenance
        localName : BHist) :
      OvertSpaceUp
  deriving DecidableEq

def overtSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: overtSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: overtSpaceEncodeBHist h

def overtSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (overtSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (overtSpaceDecodeBHist tail)

private theorem OvertSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, overtSpaceDecodeBHist (overtSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def overtSpaceFields : OvertSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OvertSpaceUp.mk space basis positivity witness locatedReal compactHandoff transport replay
      provenance localName =>
      [space, basis, positivity, witness, locatedReal, compactHandoff, transport, replay,
        provenance, localName]

def overtSpaceToEventFlow : OvertSpaceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (overtSpaceFields x).map overtSpaceEncodeBHist

private def overtSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => overtSpaceEventAtDefault index rest

def overtSpaceFromEventFlow : EventFlow → Option OvertSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (OvertSpaceUp.mk
        (overtSpaceDecodeBHist (overtSpaceEventAtDefault 0 ef))
        (overtSpaceDecodeBHist (overtSpaceEventAtDefault 1 ef))
        (overtSpaceDecodeBHist (overtSpaceEventAtDefault 2 ef))
        (overtSpaceDecodeBHist (overtSpaceEventAtDefault 3 ef))
        (overtSpaceDecodeBHist (overtSpaceEventAtDefault 4 ef))
        (overtSpaceDecodeBHist (overtSpaceEventAtDefault 5 ef))
        (overtSpaceDecodeBHist (overtSpaceEventAtDefault 6 ef))
        (overtSpaceDecodeBHist (overtSpaceEventAtDefault 7 ef))
        (overtSpaceDecodeBHist (overtSpaceEventAtDefault 8 ef))
        (overtSpaceDecodeBHist (overtSpaceEventAtDefault 9 ef)))

def overtSpaceCarrier : BHistCarrier OvertSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := overtSpaceToEventFlow
  fromEventFlow := overtSpaceFromEventFlow

instance overtSpaceBHistCarrier : BHistCarrier OvertSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  overtSpaceCarrier

private theorem OvertSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : OvertSpaceUp, overtSpaceFromEventFlow (overtSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk space basis positivity witness locatedReal compactHandoff transport replay provenance
      localName =>
      change
        some
            (OvertSpaceUp.mk
              (overtSpaceDecodeBHist (overtSpaceEncodeBHist space))
              (overtSpaceDecodeBHist (overtSpaceEncodeBHist basis))
              (overtSpaceDecodeBHist (overtSpaceEncodeBHist positivity))
              (overtSpaceDecodeBHist (overtSpaceEncodeBHist witness))
              (overtSpaceDecodeBHist (overtSpaceEncodeBHist locatedReal))
              (overtSpaceDecodeBHist (overtSpaceEncodeBHist compactHandoff))
              (overtSpaceDecodeBHist (overtSpaceEncodeBHist transport))
              (overtSpaceDecodeBHist (overtSpaceEncodeBHist replay))
              (overtSpaceDecodeBHist (overtSpaceEncodeBHist provenance))
              (overtSpaceDecodeBHist (overtSpaceEncodeBHist localName))) =
          some
            (OvertSpaceUp.mk space basis positivity witness locatedReal compactHandoff
              transport replay provenance localName)
      rw [OvertSpaceTasteGate_single_carrier_alignment_decode_encode space]
      rw [OvertSpaceTasteGate_single_carrier_alignment_decode_encode basis]
      rw [OvertSpaceTasteGate_single_carrier_alignment_decode_encode positivity]
      rw [OvertSpaceTasteGate_single_carrier_alignment_decode_encode witness]
      rw [OvertSpaceTasteGate_single_carrier_alignment_decode_encode locatedReal]
      rw [OvertSpaceTasteGate_single_carrier_alignment_decode_encode compactHandoff]
      rw [OvertSpaceTasteGate_single_carrier_alignment_decode_encode transport]
      rw [OvertSpaceTasteGate_single_carrier_alignment_decode_encode replay]
      rw [OvertSpaceTasteGate_single_carrier_alignment_decode_encode provenance]
      rw [OvertSpaceTasteGate_single_carrier_alignment_decode_encode localName]

private theorem OvertSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : OvertSpaceUp} :
    overtSpaceToEventFlow x = overtSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = overtSpaceFromEventFlow (overtSpaceToEventFlow x) :=
        (OvertSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      _ = overtSpaceFromEventFlow (overtSpaceToEventFlow y) :=
        congrArg overtSpaceFromEventFlow hxy
      _ = some y := OvertSpaceTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

def overtSpaceGate : @ChapterTasteGate OvertSpaceUp overtSpaceCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change overtSpaceFromEventFlow (overtSpaceToEventFlow x) = some x
    exact OvertSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (OvertSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance overtSpaceChapterTasteGate : ChapterTasteGate OvertSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  overtSpaceGate

theorem OvertSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, overtSpaceDecodeBHist (overtSpaceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier OvertSpaceUp) ∧ Nonempty (ChapterTasteGate OvertSpaceUp) ∧
        overtSpaceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨OvertSpaceTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨overtSpaceCarrier⟩, ⟨⟨overtSpaceGate⟩, rfl⟩⟩⟩

end BEDC.Derived.OvertSpaceUp
