import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NestedIntervalSelectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NestedIntervalSelectionUp : Type where
  | mk (I L B W R D Q E H C P N : BHist) : NestedIntervalSelectionUp
  deriving DecidableEq

def nestedIntervalSelectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nestedIntervalSelectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nestedIntervalSelectionEncodeBHist h

def nestedIntervalSelectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nestedIntervalSelectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nestedIntervalSelectionDecodeBHist tail)

private theorem NestedIntervalSelectionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      nestedIntervalSelectionDecodeBHist (nestedIntervalSelectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def nestedIntervalSelectionFields : NestedIntervalSelectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NestedIntervalSelectionUp.mk I L B W R D Q E H C P N =>
      [I, L, B, W, R, D, Q, E, H, C, P, N]

def nestedIntervalSelectionToEventFlow : NestedIntervalSelectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map nestedIntervalSelectionEncodeBHist (nestedIntervalSelectionFields x)

private def nestedIntervalSelectionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => nestedIntervalSelectionEventAt index rest

def nestedIntervalSelectionFromEventFlow : EventFlow → Option NestedIntervalSelectionUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (NestedIntervalSelectionUp.mk
          (nestedIntervalSelectionDecodeBHist (nestedIntervalSelectionEventAt 0 ef))
          (nestedIntervalSelectionDecodeBHist (nestedIntervalSelectionEventAt 1 ef))
          (nestedIntervalSelectionDecodeBHist (nestedIntervalSelectionEventAt 2 ef))
          (nestedIntervalSelectionDecodeBHist (nestedIntervalSelectionEventAt 3 ef))
          (nestedIntervalSelectionDecodeBHist (nestedIntervalSelectionEventAt 4 ef))
          (nestedIntervalSelectionDecodeBHist (nestedIntervalSelectionEventAt 5 ef))
          (nestedIntervalSelectionDecodeBHist (nestedIntervalSelectionEventAt 6 ef))
          (nestedIntervalSelectionDecodeBHist (nestedIntervalSelectionEventAt 7 ef))
          (nestedIntervalSelectionDecodeBHist (nestedIntervalSelectionEventAt 8 ef))
          (nestedIntervalSelectionDecodeBHist (nestedIntervalSelectionEventAt 9 ef))
          (nestedIntervalSelectionDecodeBHist (nestedIntervalSelectionEventAt 10 ef))
          (nestedIntervalSelectionDecodeBHist (nestedIntervalSelectionEventAt 11 ef)))

private theorem NestedIntervalSelectionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : NestedIntervalSelectionUp,
      nestedIntervalSelectionFromEventFlow (nestedIntervalSelectionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I L B W R D Q E H C P N =>
      change
        some
          (NestedIntervalSelectionUp.mk
            (nestedIntervalSelectionDecodeBHist (nestedIntervalSelectionEncodeBHist I))
            (nestedIntervalSelectionDecodeBHist (nestedIntervalSelectionEncodeBHist L))
            (nestedIntervalSelectionDecodeBHist (nestedIntervalSelectionEncodeBHist B))
            (nestedIntervalSelectionDecodeBHist (nestedIntervalSelectionEncodeBHist W))
            (nestedIntervalSelectionDecodeBHist (nestedIntervalSelectionEncodeBHist R))
            (nestedIntervalSelectionDecodeBHist (nestedIntervalSelectionEncodeBHist D))
            (nestedIntervalSelectionDecodeBHist (nestedIntervalSelectionEncodeBHist Q))
            (nestedIntervalSelectionDecodeBHist (nestedIntervalSelectionEncodeBHist E))
            (nestedIntervalSelectionDecodeBHist (nestedIntervalSelectionEncodeBHist H))
            (nestedIntervalSelectionDecodeBHist (nestedIntervalSelectionEncodeBHist C))
            (nestedIntervalSelectionDecodeBHist (nestedIntervalSelectionEncodeBHist P))
            (nestedIntervalSelectionDecodeBHist (nestedIntervalSelectionEncodeBHist N))) =
          some (NestedIntervalSelectionUp.mk I L B W R D Q E H C P N)
      rw [NestedIntervalSelectionTasteGate_single_carrier_alignment_decode I,
        NestedIntervalSelectionTasteGate_single_carrier_alignment_decode L,
        NestedIntervalSelectionTasteGate_single_carrier_alignment_decode B,
        NestedIntervalSelectionTasteGate_single_carrier_alignment_decode W,
        NestedIntervalSelectionTasteGate_single_carrier_alignment_decode R,
        NestedIntervalSelectionTasteGate_single_carrier_alignment_decode D,
        NestedIntervalSelectionTasteGate_single_carrier_alignment_decode Q,
        NestedIntervalSelectionTasteGate_single_carrier_alignment_decode E,
        NestedIntervalSelectionTasteGate_single_carrier_alignment_decode H,
        NestedIntervalSelectionTasteGate_single_carrier_alignment_decode C,
        NestedIntervalSelectionTasteGate_single_carrier_alignment_decode P,
        NestedIntervalSelectionTasteGate_single_carrier_alignment_decode N]

private theorem NestedIntervalSelectionTasteGate_single_carrier_alignment_injective
    {x y : NestedIntervalSelectionUp} :
    nestedIntervalSelectionToEventFlow x = nestedIntervalSelectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      nestedIntervalSelectionFromEventFlow (nestedIntervalSelectionToEventFlow x) =
        nestedIntervalSelectionFromEventFlow (nestedIntervalSelectionToEventFlow y) :=
    congrArg nestedIntervalSelectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (NestedIntervalSelectionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (NestedIntervalSelectionTasteGate_single_carrier_alignment_round_trip y)))

private theorem nestedIntervalSelectionFieldFaithful :
    ∀ x y : NestedIntervalSelectionUp,
      nestedIntervalSelectionFields x = nestedIntervalSelectionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk I1 L1 B1 W1 R1 D1 Q1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 L2 B2 W2 R2 D2 Q2 E2 H2 C2 P2 N2 =>
          cases h
          rfl

instance nestedIntervalSelectionBHistCarrier :
    BHistCarrier NestedIntervalSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nestedIntervalSelectionToEventFlow
  fromEventFlow := nestedIntervalSelectionFromEventFlow

instance nestedIntervalSelectionChapterTasteGate :
    ChapterTasteGate NestedIntervalSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      nestedIntervalSelectionFromEventFlow (nestedIntervalSelectionToEventFlow x) = some x
    exact NestedIntervalSelectionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (NestedIntervalSelectionTasteGate_single_carrier_alignment_injective heq)

instance nestedIntervalSelectionFieldFaithfulInstance :
    FieldFaithful NestedIntervalSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := nestedIntervalSelectionFields
  field_faithful := nestedIntervalSelectionFieldFaithful

instance nestedIntervalSelectionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial NestedIntervalSelectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨NestedIntervalSelectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      NestedIntervalSelectionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate NestedIntervalSelectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  nestedIntervalSelectionChapterTasteGate

def taste_gate_witness : FieldFaithful NestedIntervalSelectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  nestedIntervalSelectionFieldFaithfulInstance

theorem NestedIntervalSelectionTasteGate_single_carrier_alignment :
    (∀ h : BHist, nestedIntervalSelectionDecodeBHist (nestedIntervalSelectionEncodeBHist h) = h) ∧
      nestedIntervalSelectionFields
          (NestedIntervalSelectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact ⟨NestedIntervalSelectionTasteGate_single_carrier_alignment_decode, rfl⟩

end BEDC.Derived.NestedIntervalSelectionUp
