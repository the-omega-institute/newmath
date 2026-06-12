import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteDifferenceTableUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteDifferenceTableUp : Type where
  | mk (S W R D L E H C P N : BHist) : FiniteDifferenceTableUp
  deriving DecidableEq

def finiteDifferenceTableEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteDifferenceTableEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteDifferenceTableEncodeBHist h

def finiteDifferenceTableDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteDifferenceTableDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteDifferenceTableDecodeBHist tail)

private theorem FiniteDifferenceTableTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      finiteDifferenceTableDecodeBHist (finiteDifferenceTableEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteDifferenceTableFields : FiniteDifferenceTableUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteDifferenceTableUp.mk S W R D L E H C P N => [S, W, R, D, L, E, H, C, P, N]

def finiteDifferenceTableToEventFlow : FiniteDifferenceTableUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteDifferenceTableFields x).map finiteDifferenceTableEncodeBHist

private def finiteDifferenceTableEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteDifferenceTableEventAt index rest

def finiteDifferenceTableFromEventFlow (ef : EventFlow) :
    Option FiniteDifferenceTableUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteDifferenceTableUp.mk
      (finiteDifferenceTableDecodeBHist (finiteDifferenceTableEventAt 0 ef))
      (finiteDifferenceTableDecodeBHist (finiteDifferenceTableEventAt 1 ef))
      (finiteDifferenceTableDecodeBHist (finiteDifferenceTableEventAt 2 ef))
      (finiteDifferenceTableDecodeBHist (finiteDifferenceTableEventAt 3 ef))
      (finiteDifferenceTableDecodeBHist (finiteDifferenceTableEventAt 4 ef))
      (finiteDifferenceTableDecodeBHist (finiteDifferenceTableEventAt 5 ef))
      (finiteDifferenceTableDecodeBHist (finiteDifferenceTableEventAt 6 ef))
      (finiteDifferenceTableDecodeBHist (finiteDifferenceTableEventAt 7 ef))
      (finiteDifferenceTableDecodeBHist (finiteDifferenceTableEventAt 8 ef))
      (finiteDifferenceTableDecodeBHist (finiteDifferenceTableEventAt 9 ef)))

private theorem FiniteDifferenceTableTasteGate_single_carrier_alignment_round_trip
    (x : FiniteDifferenceTableUp) :
    finiteDifferenceTableFromEventFlow (finiteDifferenceTableToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S W R D L E H C P N =>
      change
        some
          (FiniteDifferenceTableUp.mk
            (finiteDifferenceTableDecodeBHist (finiteDifferenceTableEncodeBHist S))
            (finiteDifferenceTableDecodeBHist (finiteDifferenceTableEncodeBHist W))
            (finiteDifferenceTableDecodeBHist (finiteDifferenceTableEncodeBHist R))
            (finiteDifferenceTableDecodeBHist (finiteDifferenceTableEncodeBHist D))
            (finiteDifferenceTableDecodeBHist (finiteDifferenceTableEncodeBHist L))
            (finiteDifferenceTableDecodeBHist (finiteDifferenceTableEncodeBHist E))
            (finiteDifferenceTableDecodeBHist (finiteDifferenceTableEncodeBHist H))
            (finiteDifferenceTableDecodeBHist (finiteDifferenceTableEncodeBHist C))
            (finiteDifferenceTableDecodeBHist (finiteDifferenceTableEncodeBHist P))
            (finiteDifferenceTableDecodeBHist (finiteDifferenceTableEncodeBHist N))) =
          some (FiniteDifferenceTableUp.mk S W R D L E H C P N)
      rw [FiniteDifferenceTableTasteGate_single_carrier_alignment_decode_encode S,
        FiniteDifferenceTableTasteGate_single_carrier_alignment_decode_encode W,
        FiniteDifferenceTableTasteGate_single_carrier_alignment_decode_encode R,
        FiniteDifferenceTableTasteGate_single_carrier_alignment_decode_encode D,
        FiniteDifferenceTableTasteGate_single_carrier_alignment_decode_encode L,
        FiniteDifferenceTableTasteGate_single_carrier_alignment_decode_encode E,
        FiniteDifferenceTableTasteGate_single_carrier_alignment_decode_encode H,
        FiniteDifferenceTableTasteGate_single_carrier_alignment_decode_encode C,
        FiniteDifferenceTableTasteGate_single_carrier_alignment_decode_encode P,
        FiniteDifferenceTableTasteGate_single_carrier_alignment_decode_encode N]

private theorem FiniteDifferenceTableTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteDifferenceTableUp} :
    finiteDifferenceTableToEventFlow x = finiteDifferenceTableToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteDifferenceTableFromEventFlow (finiteDifferenceTableToEventFlow x) =
        finiteDifferenceTableFromEventFlow (finiteDifferenceTableToEventFlow y) :=
    congrArg finiteDifferenceTableFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteDifferenceTableTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FiniteDifferenceTableTasteGate_single_carrier_alignment_round_trip y)))

private theorem FiniteDifferenceTableTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : FiniteDifferenceTableUp,
      finiteDifferenceTableFields x = finiteDifferenceTableFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 W1 R1 D1 L1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 W2 R2 D2 L2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance finiteDifferenceTableBHistCarrier : BHistCarrier FiniteDifferenceTableUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteDifferenceTableToEventFlow
  fromEventFlow := finiteDifferenceTableFromEventFlow

instance finiteDifferenceTableChapterTasteGate :
    ChapterTasteGate FiniteDifferenceTableUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteDifferenceTableFromEventFlow (finiteDifferenceTableToEventFlow x) = some x
    exact FiniteDifferenceTableTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteDifferenceTableTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance finiteDifferenceTableFieldFaithful :
    FieldFaithful FiniteDifferenceTableUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteDifferenceTableFields
  field_faithful := FiniteDifferenceTableTasteGate_single_carrier_alignment_fields_faithful

instance finiteDifferenceTableNontrivial : Nontrivial FiniteDifferenceTableUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteDifferenceTableUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      FiniteDifferenceTableUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def FiniteDifferenceTableTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate FiniteDifferenceTableUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteDifferenceTableChapterTasteGate

theorem FiniteDifferenceTableTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finiteDifferenceTableDecodeBHist (finiteDifferenceTableEncodeBHist h) = h) ∧
      (∀ x : FiniteDifferenceTableUp,
        finiteDifferenceTableFromEventFlow (finiteDifferenceTableToEventFlow x) = some x) ∧
        (∀ x y : FiniteDifferenceTableUp,
          finiteDifferenceTableToEventFlow x = finiteDifferenceTableToEventFlow y → x = y) ∧
          finiteDifferenceTableEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨FiniteDifferenceTableTasteGate_single_carrier_alignment_decode_encode,
      FiniteDifferenceTableTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        FiniteDifferenceTableTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FiniteDifferenceTableUp
