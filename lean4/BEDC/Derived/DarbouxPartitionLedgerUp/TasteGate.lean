import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DarbouxPartitionLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DarbouxPartitionLedgerUp : Type where
  | mk (I C E R W S H K P N : BHist) : DarbouxPartitionLedgerUp
  deriving DecidableEq

def darbouxPartitionLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: darbouxPartitionLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: darbouxPartitionLedgerEncodeBHist h

def darbouxPartitionLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (darbouxPartitionLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (darbouxPartitionLedgerDecodeBHist tail)

private theorem DarbouxPartitionLedgerTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      darbouxPartitionLedgerDecodeBHist (darbouxPartitionLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def darbouxPartitionLedgerFields : DarbouxPartitionLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DarbouxPartitionLedgerUp.mk I C E R W S H K P N => [I, C, E, R, W, S, H, K, P, N]

def darbouxPartitionLedgerToEventFlow : DarbouxPartitionLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (darbouxPartitionLedgerFields x).map darbouxPartitionLedgerEncodeBHist

private def darbouxPartitionLedgerEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => darbouxPartitionLedgerEventAtDefault index rest

def darbouxPartitionLedgerFromEventFlow (ef : EventFlow) : Option DarbouxPartitionLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DarbouxPartitionLedgerUp.mk
      (darbouxPartitionLedgerDecodeBHist (darbouxPartitionLedgerEventAtDefault 0 ef))
      (darbouxPartitionLedgerDecodeBHist (darbouxPartitionLedgerEventAtDefault 1 ef))
      (darbouxPartitionLedgerDecodeBHist (darbouxPartitionLedgerEventAtDefault 2 ef))
      (darbouxPartitionLedgerDecodeBHist (darbouxPartitionLedgerEventAtDefault 3 ef))
      (darbouxPartitionLedgerDecodeBHist (darbouxPartitionLedgerEventAtDefault 4 ef))
      (darbouxPartitionLedgerDecodeBHist (darbouxPartitionLedgerEventAtDefault 5 ef))
      (darbouxPartitionLedgerDecodeBHist (darbouxPartitionLedgerEventAtDefault 6 ef))
      (darbouxPartitionLedgerDecodeBHist (darbouxPartitionLedgerEventAtDefault 7 ef))
      (darbouxPartitionLedgerDecodeBHist (darbouxPartitionLedgerEventAtDefault 8 ef))
      (darbouxPartitionLedgerDecodeBHist (darbouxPartitionLedgerEventAtDefault 9 ef)))

private theorem DarbouxPartitionLedgerTasteGate_single_carrier_alignment_round_trip
    (x : DarbouxPartitionLedgerUp) :
    darbouxPartitionLedgerFromEventFlow (darbouxPartitionLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I C E R W S H K P N =>
      change
        some
          (DarbouxPartitionLedgerUp.mk
            (darbouxPartitionLedgerDecodeBHist (darbouxPartitionLedgerEncodeBHist I))
            (darbouxPartitionLedgerDecodeBHist (darbouxPartitionLedgerEncodeBHist C))
            (darbouxPartitionLedgerDecodeBHist (darbouxPartitionLedgerEncodeBHist E))
            (darbouxPartitionLedgerDecodeBHist (darbouxPartitionLedgerEncodeBHist R))
            (darbouxPartitionLedgerDecodeBHist (darbouxPartitionLedgerEncodeBHist W))
            (darbouxPartitionLedgerDecodeBHist (darbouxPartitionLedgerEncodeBHist S))
            (darbouxPartitionLedgerDecodeBHist (darbouxPartitionLedgerEncodeBHist H))
            (darbouxPartitionLedgerDecodeBHist (darbouxPartitionLedgerEncodeBHist K))
            (darbouxPartitionLedgerDecodeBHist (darbouxPartitionLedgerEncodeBHist P))
            (darbouxPartitionLedgerDecodeBHist (darbouxPartitionLedgerEncodeBHist N))) =
          some (DarbouxPartitionLedgerUp.mk I C E R W S H K P N)
      rw [DarbouxPartitionLedgerTasteGate_single_carrier_alignment_decode I,
        DarbouxPartitionLedgerTasteGate_single_carrier_alignment_decode C,
        DarbouxPartitionLedgerTasteGate_single_carrier_alignment_decode E,
        DarbouxPartitionLedgerTasteGate_single_carrier_alignment_decode R,
        DarbouxPartitionLedgerTasteGate_single_carrier_alignment_decode W,
        DarbouxPartitionLedgerTasteGate_single_carrier_alignment_decode S,
        DarbouxPartitionLedgerTasteGate_single_carrier_alignment_decode H,
        DarbouxPartitionLedgerTasteGate_single_carrier_alignment_decode K,
        DarbouxPartitionLedgerTasteGate_single_carrier_alignment_decode P,
        DarbouxPartitionLedgerTasteGate_single_carrier_alignment_decode N]

private theorem DarbouxPartitionLedgerTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DarbouxPartitionLedgerUp} :
    darbouxPartitionLedgerToEventFlow x = darbouxPartitionLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      darbouxPartitionLedgerFromEventFlow (darbouxPartitionLedgerToEventFlow x) =
        darbouxPartitionLedgerFromEventFlow (darbouxPartitionLedgerToEventFlow y) :=
    congrArg darbouxPartitionLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DarbouxPartitionLedgerTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DarbouxPartitionLedgerTasteGate_single_carrier_alignment_round_trip y)))

private theorem DarbouxPartitionLedgerTasteGate_single_carrier_alignment_fields :
    ∀ x y : DarbouxPartitionLedgerUp, darbouxPartitionLedgerFields x =
      darbouxPartitionLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ C₁ E₁ R₁ W₁ S₁ H₁ K₁ P₁ N₁ =>
      cases y with
      | mk I₂ C₂ E₂ R₂ W₂ S₂ H₂ K₂ P₂ N₂ =>
          cases hfields
          rfl

instance darbouxPartitionLedgerBHistCarrier : BHistCarrier DarbouxPartitionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := darbouxPartitionLedgerToEventFlow
  fromEventFlow := darbouxPartitionLedgerFromEventFlow

instance darbouxPartitionLedgerChapterTasteGate :
    ChapterTasteGate DarbouxPartitionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change darbouxPartitionLedgerFromEventFlow (darbouxPartitionLedgerToEventFlow x) = some x
    exact DarbouxPartitionLedgerTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DarbouxPartitionLedgerTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance darbouxPartitionLedgerFieldFaithful : FieldFaithful DarbouxPartitionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := darbouxPartitionLedgerFields
  field_faithful := DarbouxPartitionLedgerTasteGate_single_carrier_alignment_fields

instance darbouxPartitionLedgerNontrivial : Nontrivial DarbouxPartitionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DarbouxPartitionLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DarbouxPartitionLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DarbouxPartitionLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  darbouxPartitionLedgerChapterTasteGate

theorem DarbouxPartitionLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist, darbouxPartitionLedgerDecodeBHist (darbouxPartitionLedgerEncodeBHist h) = h) ∧
      (∀ x : DarbouxPartitionLedgerUp,
        darbouxPartitionLedgerFromEventFlow (darbouxPartitionLedgerToEventFlow x) = some x) ∧
        (∀ x y : DarbouxPartitionLedgerUp,
          darbouxPartitionLedgerToEventFlow x = darbouxPartitionLedgerToEventFlow y → x = y) ∧
          darbouxPartitionLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨DarbouxPartitionLedgerTasteGate_single_carrier_alignment_decode,
      DarbouxPartitionLedgerTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => DarbouxPartitionLedgerTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DarbouxPartitionLedgerUp
