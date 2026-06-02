import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CharacterTableUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CharacterTableUp : Type where
  | mk (G C I V Omega H P N : BHist) : CharacterTableUp
  deriving DecidableEq

def characterTableEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: characterTableEncodeBHist h
  | BHist.e1 h => BMark.b1 :: characterTableEncodeBHist h

def characterTableDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (characterTableDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (characterTableDecodeBHist tail)

private theorem CharacterTableTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, characterTableDecodeBHist (characterTableEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CharacterTableTasteGate_single_carrier_alignment_fields : CharacterTableUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CharacterTableUp.mk G C I V Omega H P N => [G, C, I, V, Omega, H, P, N]

def characterTableToEventFlow : CharacterTableUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (CharacterTableTasteGate_single_carrier_alignment_fields x).map
        characterTableEncodeBHist

private def characterTableEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => characterTableEventAtDefault index rest

def characterTableFromEventFlow (ef : EventFlow) : Option CharacterTableUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CharacterTableUp.mk
      (characterTableDecodeBHist (characterTableEventAtDefault 0 ef))
      (characterTableDecodeBHist (characterTableEventAtDefault 1 ef))
      (characterTableDecodeBHist (characterTableEventAtDefault 2 ef))
      (characterTableDecodeBHist (characterTableEventAtDefault 3 ef))
      (characterTableDecodeBHist (characterTableEventAtDefault 4 ef))
      (characterTableDecodeBHist (characterTableEventAtDefault 5 ef))
      (characterTableDecodeBHist (characterTableEventAtDefault 6 ef))
      (characterTableDecodeBHist (characterTableEventAtDefault 7 ef)))

private theorem CharacterTableTasteGate_single_carrier_alignment_round_trip
    (x : CharacterTableUp) :
    characterTableFromEventFlow (characterTableToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk G C I V Omega H P N =>
      change
        some
          (CharacterTableUp.mk
            (characterTableDecodeBHist (characterTableEncodeBHist G))
            (characterTableDecodeBHist (characterTableEncodeBHist C))
            (characterTableDecodeBHist (characterTableEncodeBHist I))
            (characterTableDecodeBHist (characterTableEncodeBHist V))
            (characterTableDecodeBHist (characterTableEncodeBHist Omega))
            (characterTableDecodeBHist (characterTableEncodeBHist H))
            (characterTableDecodeBHist (characterTableEncodeBHist P))
            (characterTableDecodeBHist (characterTableEncodeBHist N))) =
          some (CharacterTableUp.mk G C I V Omega H P N)
      rw [CharacterTableTasteGate_single_carrier_alignment_decode_encode G,
        CharacterTableTasteGate_single_carrier_alignment_decode_encode C,
        CharacterTableTasteGate_single_carrier_alignment_decode_encode I,
        CharacterTableTasteGate_single_carrier_alignment_decode_encode V,
        CharacterTableTasteGate_single_carrier_alignment_decode_encode Omega,
        CharacterTableTasteGate_single_carrier_alignment_decode_encode H,
        CharacterTableTasteGate_single_carrier_alignment_decode_encode P,
        CharacterTableTasteGate_single_carrier_alignment_decode_encode N]

private theorem CharacterTableTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CharacterTableUp} :
    characterTableToEventFlow x = characterTableToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      characterTableFromEventFlow (characterTableToEventFlow x) =
        characterTableFromEventFlow (characterTableToEventFlow y) :=
    congrArg characterTableFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CharacterTableTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CharacterTableTasteGate_single_carrier_alignment_round_trip y)))

instance characterTableBHistCarrier : BHistCarrier CharacterTableUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := characterTableToEventFlow
  fromEventFlow := characterTableFromEventFlow

instance characterTableChapterTasteGate : ChapterTasteGate CharacterTableUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change characterTableFromEventFlow (characterTableToEventFlow x) = some x
    exact CharacterTableTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CharacterTableTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CharacterTableUp :=
  -- BEDC touchpoint anchor: BHist BMark
  characterTableChapterTasteGate

theorem CharacterTableTasteGate_single_carrier_alignment :
    (∀ h : BHist, characterTableDecodeBHist (characterTableEncodeBHist h) = h) ∧
      CharacterTableTasteGate_single_carrier_alignment_fields
          (CharacterTableUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CharacterTableTasteGate_single_carrier_alignment_decode_encode,
      rfl⟩

end BEDC.Derived.CharacterTableUp
