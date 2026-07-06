import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EulerMaclaurinFiniteSumUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EulerMaclaurinFiniteSumUp : Type where
  | mk (W L U B D Q R Z H C P N : BHist) : EulerMaclaurinFiniteSumUp
  deriving DecidableEq

def eulerMaclaurinFiniteSumEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: eulerMaclaurinFiniteSumEncodeBHist h
  | BHist.e1 h => BMark.b1 :: eulerMaclaurinFiniteSumEncodeBHist h

def eulerMaclaurinFiniteSumDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (eulerMaclaurinFiniteSumDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (eulerMaclaurinFiniteSumDecodeBHist tail)

theorem EulerMaclaurinFiniteSumTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      eulerMaclaurinFiniteSumDecodeBHist (eulerMaclaurinFiniteSumEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def eulerMaclaurinFiniteSumFields :
    EulerMaclaurinFiniteSumUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EulerMaclaurinFiniteSumUp.mk W L U B D Q R Z H C P N =>
      [W, L, U, B, D, Q, R, Z, H, C, P, N]

def eulerMaclaurinFiniteSumToEventFlow :
    EulerMaclaurinFiniteSumUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (eulerMaclaurinFiniteSumFields x).map eulerMaclaurinFiniteSumEncodeBHist

private def eulerMaclaurinFiniteSumEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => eulerMaclaurinFiniteSumEventAt index rest

def eulerMaclaurinFiniteSumFromEventFlow :
    EventFlow -> Option EulerMaclaurinFiniteSumUp := fun ef =>
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EulerMaclaurinFiniteSumUp.mk
      (eulerMaclaurinFiniteSumDecodeBHist (eulerMaclaurinFiniteSumEventAt 0 ef))
      (eulerMaclaurinFiniteSumDecodeBHist (eulerMaclaurinFiniteSumEventAt 1 ef))
      (eulerMaclaurinFiniteSumDecodeBHist (eulerMaclaurinFiniteSumEventAt 2 ef))
      (eulerMaclaurinFiniteSumDecodeBHist (eulerMaclaurinFiniteSumEventAt 3 ef))
      (eulerMaclaurinFiniteSumDecodeBHist (eulerMaclaurinFiniteSumEventAt 4 ef))
      (eulerMaclaurinFiniteSumDecodeBHist (eulerMaclaurinFiniteSumEventAt 5 ef))
      (eulerMaclaurinFiniteSumDecodeBHist (eulerMaclaurinFiniteSumEventAt 6 ef))
      (eulerMaclaurinFiniteSumDecodeBHist (eulerMaclaurinFiniteSumEventAt 7 ef))
      (eulerMaclaurinFiniteSumDecodeBHist (eulerMaclaurinFiniteSumEventAt 8 ef))
      (eulerMaclaurinFiniteSumDecodeBHist (eulerMaclaurinFiniteSumEventAt 9 ef))
      (eulerMaclaurinFiniteSumDecodeBHist (eulerMaclaurinFiniteSumEventAt 10 ef))
      (eulerMaclaurinFiniteSumDecodeBHist (eulerMaclaurinFiniteSumEventAt 11 ef)))

theorem EulerMaclaurinFiniteSumTasteGate_single_carrier_alignment_round_trip
    (x : EulerMaclaurinFiniteSumUp) :
    eulerMaclaurinFiniteSumFromEventFlow
      (eulerMaclaurinFiniteSumToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk W L U B D Q R Z H C P N =>
      change
        some
          (EulerMaclaurinFiniteSumUp.mk
            (eulerMaclaurinFiniteSumDecodeBHist
              (eulerMaclaurinFiniteSumEncodeBHist W))
            (eulerMaclaurinFiniteSumDecodeBHist
              (eulerMaclaurinFiniteSumEncodeBHist L))
            (eulerMaclaurinFiniteSumDecodeBHist
              (eulerMaclaurinFiniteSumEncodeBHist U))
            (eulerMaclaurinFiniteSumDecodeBHist
              (eulerMaclaurinFiniteSumEncodeBHist B))
            (eulerMaclaurinFiniteSumDecodeBHist
              (eulerMaclaurinFiniteSumEncodeBHist D))
            (eulerMaclaurinFiniteSumDecodeBHist
              (eulerMaclaurinFiniteSumEncodeBHist Q))
            (eulerMaclaurinFiniteSumDecodeBHist
              (eulerMaclaurinFiniteSumEncodeBHist R))
            (eulerMaclaurinFiniteSumDecodeBHist
              (eulerMaclaurinFiniteSumEncodeBHist Z))
            (eulerMaclaurinFiniteSumDecodeBHist
              (eulerMaclaurinFiniteSumEncodeBHist H))
            (eulerMaclaurinFiniteSumDecodeBHist
              (eulerMaclaurinFiniteSumEncodeBHist C))
            (eulerMaclaurinFiniteSumDecodeBHist
              (eulerMaclaurinFiniteSumEncodeBHist P))
            (eulerMaclaurinFiniteSumDecodeBHist
              (eulerMaclaurinFiniteSumEncodeBHist N))) =
          some (EulerMaclaurinFiniteSumUp.mk W L U B D Q R Z H C P N)
      rw [EulerMaclaurinFiniteSumTasteGate_single_carrier_alignment_decode_encode W,
        EulerMaclaurinFiniteSumTasteGate_single_carrier_alignment_decode_encode L,
        EulerMaclaurinFiniteSumTasteGate_single_carrier_alignment_decode_encode U,
        EulerMaclaurinFiniteSumTasteGate_single_carrier_alignment_decode_encode B,
        EulerMaclaurinFiniteSumTasteGate_single_carrier_alignment_decode_encode D,
        EulerMaclaurinFiniteSumTasteGate_single_carrier_alignment_decode_encode Q,
        EulerMaclaurinFiniteSumTasteGate_single_carrier_alignment_decode_encode R,
        EulerMaclaurinFiniteSumTasteGate_single_carrier_alignment_decode_encode Z,
        EulerMaclaurinFiniteSumTasteGate_single_carrier_alignment_decode_encode H,
        EulerMaclaurinFiniteSumTasteGate_single_carrier_alignment_decode_encode C,
        EulerMaclaurinFiniteSumTasteGate_single_carrier_alignment_decode_encode P,
        EulerMaclaurinFiniteSumTasteGate_single_carrier_alignment_decode_encode N]

theorem EulerMaclaurinFiniteSumTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : EulerMaclaurinFiniteSumUp} :
    eulerMaclaurinFiniteSumToEventFlow x =
      eulerMaclaurinFiniteSumToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      eulerMaclaurinFiniteSumFromEventFlow
          (eulerMaclaurinFiniteSumToEventFlow x) =
        eulerMaclaurinFiniteSumFromEventFlow
          (eulerMaclaurinFiniteSumToEventFlow y) :=
    congrArg eulerMaclaurinFiniteSumFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (EulerMaclaurinFiniteSumTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (EulerMaclaurinFiniteSumTasteGate_single_carrier_alignment_round_trip y)))

theorem EulerMaclaurinFiniteSumTasteGate_single_carrier_alignment_field_faithful :
    forall x y : EulerMaclaurinFiniteSumUp,
      eulerMaclaurinFiniteSumFields x = eulerMaclaurinFiniteSumFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk W1 L1 U1 B1 D1 Q1 R1 Z1 H1 C1 P1 N1 =>
      cases y with
      | mk W2 L2 U2 B2 D2 Q2 R2 Z2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance eulerMaclaurinFiniteSumBHistCarrier :
    BHistCarrier EulerMaclaurinFiniteSumUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := eulerMaclaurinFiniteSumToEventFlow
  fromEventFlow := eulerMaclaurinFiniteSumFromEventFlow

instance eulerMaclaurinFiniteSumChapterTasteGate :
    ChapterTasteGate EulerMaclaurinFiniteSumUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := EulerMaclaurinFiniteSumTasteGate_single_carrier_alignment_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (EulerMaclaurinFiniteSumTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance eulerMaclaurinFiniteSumFieldFaithful :
    FieldFaithful EulerMaclaurinFiniteSumUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := eulerMaclaurinFiniteSumFields
  field_faithful := EulerMaclaurinFiniteSumTasteGate_single_carrier_alignment_field_faithful

instance eulerMaclaurinFiniteSumNontrivial :
    BEDC.Meta.TasteGate.Nontrivial EulerMaclaurinFiniteSumUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EulerMaclaurinFiniteSumUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      EulerMaclaurinFiniteSumUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem EulerMaclaurinFiniteSumTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate EulerMaclaurinFiniteSumUp) /\
      Nonempty (FieldFaithful EulerMaclaurinFiniteSumUp) /\
        Nonempty (BEDC.Meta.TasteGate.Nontrivial EulerMaclaurinFiniteSumUp) /\
          (forall h : BHist,
            eulerMaclaurinFiniteSumDecodeBHist
              (eulerMaclaurinFiniteSumEncodeBHist h) = h) /\
            eulerMaclaurinFiniteSumEncodeBHist BHist.Empty = ([] : List BMark) /\
              (forall x : EulerMaclaurinFiniteSumUp,
                eulerMaclaurinFiniteSumFromEventFlow
                  (eulerMaclaurinFiniteSumToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨eulerMaclaurinFiniteSumChapterTasteGate⟩
  · constructor
    · exact ⟨eulerMaclaurinFiniteSumFieldFaithful⟩
    · constructor
      · exact ⟨eulerMaclaurinFiniteSumNontrivial⟩
      · constructor
        · exact EulerMaclaurinFiniteSumTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · rfl
          · exact EulerMaclaurinFiniteSumTasteGate_single_carrier_alignment_round_trip

end BEDC.Derived.EulerMaclaurinFiniteSumUp
