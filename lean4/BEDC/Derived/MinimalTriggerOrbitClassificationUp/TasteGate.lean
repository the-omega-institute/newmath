import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MinimalTriggerOrbitClassificationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MinimalTriggerOrbitClassificationUp : Type where
  | mk (B N D Q K L M H C P R : BHist) : MinimalTriggerOrbitClassificationUp
  deriving DecidableEq

def minimalTriggerOrbitClassificationEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: minimalTriggerOrbitClassificationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: minimalTriggerOrbitClassificationEncodeBHist h

def minimalTriggerOrbitClassificationDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (minimalTriggerOrbitClassificationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (minimalTriggerOrbitClassificationDecodeBHist tail)

private theorem MinimalTriggerOrbitClassificationTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      minimalTriggerOrbitClassificationDecodeBHist
        (minimalTriggerOrbitClassificationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def minimalTriggerOrbitClassificationFields :
    MinimalTriggerOrbitClassificationUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MinimalTriggerOrbitClassificationUp.mk B N D Q K L M H C P R =>
      [B, N, D, Q, K, L, M, H, C, P, R]

def minimalTriggerOrbitClassificationToEventFlow :
    MinimalTriggerOrbitClassificationUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (minimalTriggerOrbitClassificationFields x).map
        minimalTriggerOrbitClassificationEncodeBHist

private def minimalTriggerOrbitClassificationEventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      minimalTriggerOrbitClassificationEventAtDefault index rest

def minimalTriggerOrbitClassificationFromEventFlow
    (ef : EventFlow) : Option MinimalTriggerOrbitClassificationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MinimalTriggerOrbitClassificationUp.mk
      (minimalTriggerOrbitClassificationDecodeBHist
        (minimalTriggerOrbitClassificationEventAtDefault 0 ef))
      (minimalTriggerOrbitClassificationDecodeBHist
        (minimalTriggerOrbitClassificationEventAtDefault 1 ef))
      (minimalTriggerOrbitClassificationDecodeBHist
        (minimalTriggerOrbitClassificationEventAtDefault 2 ef))
      (minimalTriggerOrbitClassificationDecodeBHist
        (minimalTriggerOrbitClassificationEventAtDefault 3 ef))
      (minimalTriggerOrbitClassificationDecodeBHist
        (minimalTriggerOrbitClassificationEventAtDefault 4 ef))
      (minimalTriggerOrbitClassificationDecodeBHist
        (minimalTriggerOrbitClassificationEventAtDefault 5 ef))
      (minimalTriggerOrbitClassificationDecodeBHist
        (minimalTriggerOrbitClassificationEventAtDefault 6 ef))
      (minimalTriggerOrbitClassificationDecodeBHist
        (minimalTriggerOrbitClassificationEventAtDefault 7 ef))
      (minimalTriggerOrbitClassificationDecodeBHist
        (minimalTriggerOrbitClassificationEventAtDefault 8 ef))
      (minimalTriggerOrbitClassificationDecodeBHist
        (minimalTriggerOrbitClassificationEventAtDefault 9 ef))
      (minimalTriggerOrbitClassificationDecodeBHist
        (minimalTriggerOrbitClassificationEventAtDefault 10 ef)))

private theorem MinimalTriggerOrbitClassificationTasteGate_single_carrier_alignment_round_trip
    (x : MinimalTriggerOrbitClassificationUp) :
    minimalTriggerOrbitClassificationFromEventFlow
      (minimalTriggerOrbitClassificationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B N D Q K L M H C P R =>
      change
        some
          (MinimalTriggerOrbitClassificationUp.mk
            (minimalTriggerOrbitClassificationDecodeBHist
              (minimalTriggerOrbitClassificationEncodeBHist B))
            (minimalTriggerOrbitClassificationDecodeBHist
              (minimalTriggerOrbitClassificationEncodeBHist N))
            (minimalTriggerOrbitClassificationDecodeBHist
              (minimalTriggerOrbitClassificationEncodeBHist D))
            (minimalTriggerOrbitClassificationDecodeBHist
              (minimalTriggerOrbitClassificationEncodeBHist Q))
            (minimalTriggerOrbitClassificationDecodeBHist
              (minimalTriggerOrbitClassificationEncodeBHist K))
            (minimalTriggerOrbitClassificationDecodeBHist
              (minimalTriggerOrbitClassificationEncodeBHist L))
            (minimalTriggerOrbitClassificationDecodeBHist
              (minimalTriggerOrbitClassificationEncodeBHist M))
            (minimalTriggerOrbitClassificationDecodeBHist
              (minimalTriggerOrbitClassificationEncodeBHist H))
            (minimalTriggerOrbitClassificationDecodeBHist
              (minimalTriggerOrbitClassificationEncodeBHist C))
            (minimalTriggerOrbitClassificationDecodeBHist
              (minimalTriggerOrbitClassificationEncodeBHist P))
            (minimalTriggerOrbitClassificationDecodeBHist
              (minimalTriggerOrbitClassificationEncodeBHist R))) =
          some (MinimalTriggerOrbitClassificationUp.mk B N D Q K L M H C P R)
      rw [MinimalTriggerOrbitClassificationTasteGate_single_carrier_alignment_decode_encode B,
        MinimalTriggerOrbitClassificationTasteGate_single_carrier_alignment_decode_encode N,
        MinimalTriggerOrbitClassificationTasteGate_single_carrier_alignment_decode_encode D,
        MinimalTriggerOrbitClassificationTasteGate_single_carrier_alignment_decode_encode Q,
        MinimalTriggerOrbitClassificationTasteGate_single_carrier_alignment_decode_encode K,
        MinimalTriggerOrbitClassificationTasteGate_single_carrier_alignment_decode_encode L,
        MinimalTriggerOrbitClassificationTasteGate_single_carrier_alignment_decode_encode M,
        MinimalTriggerOrbitClassificationTasteGate_single_carrier_alignment_decode_encode H,
        MinimalTriggerOrbitClassificationTasteGate_single_carrier_alignment_decode_encode C,
        MinimalTriggerOrbitClassificationTasteGate_single_carrier_alignment_decode_encode P,
        MinimalTriggerOrbitClassificationTasteGate_single_carrier_alignment_decode_encode R]

private theorem MinimalTriggerOrbitClassificationTasteGate_single_carrier_alignment_injective
    {x y : MinimalTriggerOrbitClassificationUp} :
    minimalTriggerOrbitClassificationToEventFlow x =
      minimalTriggerOrbitClassificationToEventFlow y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      minimalTriggerOrbitClassificationFromEventFlow
          (minimalTriggerOrbitClassificationToEventFlow x) =
        minimalTriggerOrbitClassificationFromEventFlow
          (minimalTriggerOrbitClassificationToEventFlow y) :=
    congrArg minimalTriggerOrbitClassificationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MinimalTriggerOrbitClassificationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MinimalTriggerOrbitClassificationTasteGate_single_carrier_alignment_round_trip y)))

private theorem MinimalTriggerOrbitClassificationTasteGate_single_carrier_alignment_fields :
    forall x y : MinimalTriggerOrbitClassificationUp,
      minimalTriggerOrbitClassificationFields x =
        minimalTriggerOrbitClassificationFields y ->
          x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 N1 D1 Q1 K1 L1 M1 H1 C1 P1 R1 =>
      cases y with
      | mk B2 N2 D2 Q2 K2 L2 M2 H2 C2 P2 R2 =>
          cases hfields
          rfl

instance minimalTriggerOrbitClassificationBHistCarrier :
    BHistCarrier MinimalTriggerOrbitClassificationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := minimalTriggerOrbitClassificationToEventFlow
  fromEventFlow := minimalTriggerOrbitClassificationFromEventFlow

instance minimalTriggerOrbitClassificationChapterTasteGate :
    ChapterTasteGate MinimalTriggerOrbitClassificationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      minimalTriggerOrbitClassificationFromEventFlow
        (minimalTriggerOrbitClassificationToEventFlow x) = some x
    exact MinimalTriggerOrbitClassificationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MinimalTriggerOrbitClassificationTasteGate_single_carrier_alignment_injective heq)

instance minimalTriggerOrbitClassificationFieldFaithful :
    FieldFaithful MinimalTriggerOrbitClassificationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := minimalTriggerOrbitClassificationFields
  field_faithful :=
    MinimalTriggerOrbitClassificationTasteGate_single_carrier_alignment_fields

instance minimalTriggerOrbitClassificationNontrivial :
    BEDC.Meta.TasteGate.Nontrivial MinimalTriggerOrbitClassificationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MinimalTriggerOrbitClassificationUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      MinimalTriggerOrbitClassificationUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def MinimalTriggerOrbitClassificationTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate MinimalTriggerOrbitClassificationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  minimalTriggerOrbitClassificationChapterTasteGate

theorem MinimalTriggerOrbitClassificationTasteGate_single_carrier_alignment
    (B N D Q K L M H C P R : BHist) :
    minimalTriggerOrbitClassificationDecodeBHist
        (BMark.b0 :: minimalTriggerOrbitClassificationEncodeBHist B) =
      BHist.e0 B ∧
    minimalTriggerOrbitClassificationFromEventFlow
        (minimalTriggerOrbitClassificationToEventFlow
          (MinimalTriggerOrbitClassificationUp.mk B N D Q K L M H C P R)) =
      some (MinimalTriggerOrbitClassificationUp.mk B N D Q K L M H C P R) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact congrArg BHist.e0
      (MinimalTriggerOrbitClassificationTasteGate_single_carrier_alignment_decode_encode B)
  · exact MinimalTriggerOrbitClassificationTasteGate_single_carrier_alignment_round_trip
      (MinimalTriggerOrbitClassificationUp.mk B N D Q K L M H C P R)

end BEDC.Derived.MinimalTriggerOrbitClassificationUp
