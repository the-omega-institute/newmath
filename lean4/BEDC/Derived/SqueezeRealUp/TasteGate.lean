import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SqueezeRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SqueezeRealUp : Type where
  | mk (l x u epsilon L U S E P N : BHist) : SqueezeRealUp
  deriving DecidableEq

def SqueezeRealTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: SqueezeRealTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: SqueezeRealTasteGate_single_carrier_alignment_encodeBHist h

def SqueezeRealTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (SqueezeRealTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (SqueezeRealTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem SqueezeRealTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      SqueezeRealTasteGate_single_carrier_alignment_decodeBHist
        (SqueezeRealTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def SqueezeRealTasteGate_single_carrier_alignment_fields :
    SqueezeRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SqueezeRealUp.mk l x u epsilon L U S E P N => [l, x, u, epsilon, L, U, S, E, P, N]

def SqueezeRealTasteGate_single_carrier_alignment_toEventFlow :
    SqueezeRealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | q =>
      [BMark.b1, BMark.b0, BMark.b0, BMark.b0] ::
        (SqueezeRealTasteGate_single_carrier_alignment_fields q).map
          SqueezeRealTasteGate_single_carrier_alignment_encodeBHist

private def SqueezeRealTasteGate_single_carrier_alignment_event_at :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      SqueezeRealTasteGate_single_carrier_alignment_event_at index rest

def SqueezeRealTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option SqueezeRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | [BMark.b1, BMark.b0, BMark.b0, BMark.b0] :: rows =>
      some
        (SqueezeRealUp.mk
          (SqueezeRealTasteGate_single_carrier_alignment_decodeBHist
            (SqueezeRealTasteGate_single_carrier_alignment_event_at 0 rows))
          (SqueezeRealTasteGate_single_carrier_alignment_decodeBHist
            (SqueezeRealTasteGate_single_carrier_alignment_event_at 1 rows))
          (SqueezeRealTasteGate_single_carrier_alignment_decodeBHist
            (SqueezeRealTasteGate_single_carrier_alignment_event_at 2 rows))
          (SqueezeRealTasteGate_single_carrier_alignment_decodeBHist
            (SqueezeRealTasteGate_single_carrier_alignment_event_at 3 rows))
          (SqueezeRealTasteGate_single_carrier_alignment_decodeBHist
            (SqueezeRealTasteGate_single_carrier_alignment_event_at 4 rows))
          (SqueezeRealTasteGate_single_carrier_alignment_decodeBHist
            (SqueezeRealTasteGate_single_carrier_alignment_event_at 5 rows))
          (SqueezeRealTasteGate_single_carrier_alignment_decodeBHist
            (SqueezeRealTasteGate_single_carrier_alignment_event_at 6 rows))
          (SqueezeRealTasteGate_single_carrier_alignment_decodeBHist
            (SqueezeRealTasteGate_single_carrier_alignment_event_at 7 rows))
          (SqueezeRealTasteGate_single_carrier_alignment_decodeBHist
            (SqueezeRealTasteGate_single_carrier_alignment_event_at 8 rows))
          (SqueezeRealTasteGate_single_carrier_alignment_decodeBHist
            (SqueezeRealTasteGate_single_carrier_alignment_event_at 9 rows)))
  | _ => none

private theorem SqueezeRealTasteGate_single_carrier_alignment_round_trip
    (q : SqueezeRealUp) :
    SqueezeRealTasteGate_single_carrier_alignment_fromEventFlow
      (SqueezeRealTasteGate_single_carrier_alignment_toEventFlow q) = some q := by
  -- BEDC touchpoint anchor: BHist BMark
  cases q with
  | mk l x u epsilon L U S E P N =>
      change
        some
          (SqueezeRealUp.mk
            (SqueezeRealTasteGate_single_carrier_alignment_decodeBHist
              (SqueezeRealTasteGate_single_carrier_alignment_encodeBHist l))
            (SqueezeRealTasteGate_single_carrier_alignment_decodeBHist
              (SqueezeRealTasteGate_single_carrier_alignment_encodeBHist x))
            (SqueezeRealTasteGate_single_carrier_alignment_decodeBHist
              (SqueezeRealTasteGate_single_carrier_alignment_encodeBHist u))
            (SqueezeRealTasteGate_single_carrier_alignment_decodeBHist
              (SqueezeRealTasteGate_single_carrier_alignment_encodeBHist epsilon))
            (SqueezeRealTasteGate_single_carrier_alignment_decodeBHist
              (SqueezeRealTasteGate_single_carrier_alignment_encodeBHist L))
            (SqueezeRealTasteGate_single_carrier_alignment_decodeBHist
              (SqueezeRealTasteGate_single_carrier_alignment_encodeBHist U))
            (SqueezeRealTasteGate_single_carrier_alignment_decodeBHist
              (SqueezeRealTasteGate_single_carrier_alignment_encodeBHist S))
            (SqueezeRealTasteGate_single_carrier_alignment_decodeBHist
              (SqueezeRealTasteGate_single_carrier_alignment_encodeBHist E))
            (SqueezeRealTasteGate_single_carrier_alignment_decodeBHist
              (SqueezeRealTasteGate_single_carrier_alignment_encodeBHist P))
            (SqueezeRealTasteGate_single_carrier_alignment_decodeBHist
              (SqueezeRealTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (SqueezeRealUp.mk l x u epsilon L U S E P N)
      rw [SqueezeRealTasteGate_single_carrier_alignment_decode_encode l,
        SqueezeRealTasteGate_single_carrier_alignment_decode_encode x,
        SqueezeRealTasteGate_single_carrier_alignment_decode_encode u,
        SqueezeRealTasteGate_single_carrier_alignment_decode_encode epsilon,
        SqueezeRealTasteGate_single_carrier_alignment_decode_encode L,
        SqueezeRealTasteGate_single_carrier_alignment_decode_encode U,
        SqueezeRealTasteGate_single_carrier_alignment_decode_encode S,
        SqueezeRealTasteGate_single_carrier_alignment_decode_encode E,
        SqueezeRealTasteGate_single_carrier_alignment_decode_encode P,
        SqueezeRealTasteGate_single_carrier_alignment_decode_encode N]

private theorem SqueezeRealTasteGate_single_carrier_alignment_toEventFlow_injective
    {q r : SqueezeRealUp} :
    SqueezeRealTasteGate_single_carrier_alignment_toEventFlow q =
      SqueezeRealTasteGate_single_carrier_alignment_toEventFlow r → q = r := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      SqueezeRealTasteGate_single_carrier_alignment_fromEventFlow
          (SqueezeRealTasteGate_single_carrier_alignment_toEventFlow q) =
        SqueezeRealTasteGate_single_carrier_alignment_fromEventFlow
          (SqueezeRealTasteGate_single_carrier_alignment_toEventFlow r) :=
    congrArg SqueezeRealTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SqueezeRealTasteGate_single_carrier_alignment_round_trip q).symm
      (Eq.trans hread (SqueezeRealTasteGate_single_carrier_alignment_round_trip r)))

private theorem SqueezeRealTasteGate_single_carrier_alignment_fields_faithful :
    ∀ q r : SqueezeRealUp,
      SqueezeRealTasteGate_single_carrier_alignment_fields q =
        SqueezeRealTasteGate_single_carrier_alignment_fields r → q = r := by
  -- BEDC touchpoint anchor: BHist BMark
  intro q r hfields
  cases q with
  | mk l₁ x₁ u₁ epsilon₁ L₁ U₁ S₁ E₁ P₁ N₁ =>
      cases r with
      | mk l₂ x₂ u₂ epsilon₂ L₂ U₂ S₂ E₂ P₂ N₂ =>
          cases hfields
          rfl

instance SqueezeRealTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier SqueezeRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := SqueezeRealTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := SqueezeRealTasteGate_single_carrier_alignment_fromEventFlow

instance SqueezeRealTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate SqueezeRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro q
    change
      SqueezeRealTasteGate_single_carrier_alignment_fromEventFlow
        (SqueezeRealTasteGate_single_carrier_alignment_toEventFlow q) = some q
    exact SqueezeRealTasteGate_single_carrier_alignment_round_trip q
  layer_separation := by
    intro q r hqr heq
    exact hqr (SqueezeRealTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance SqueezeRealTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful SqueezeRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := SqueezeRealTasteGate_single_carrier_alignment_fields
  field_faithful := SqueezeRealTasteGate_single_carrier_alignment_fields_faithful

def SqueezeRealTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate SqueezeRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  SqueezeRealTasteGate_single_carrier_alignment_ChapterTasteGate

theorem SqueezeRealTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      SqueezeRealTasteGate_single_carrier_alignment_decodeBHist
        (SqueezeRealTasteGate_single_carrier_alignment_encodeBHist h) = h) ∧
      SqueezeRealTasteGate_single_carrier_alignment_fields
          (SqueezeRealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] ∧
      SqueezeRealTasteGate_single_carrier_alignment_toEventFlow
          (SqueezeRealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [[BMark.b1, BMark.b0, BMark.b0, BMark.b0], [], [], [], [], [], [], [], [], [], []] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact SqueezeRealTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · rfl
    · rfl

end BEDC.Derived.SqueezeRealUp
