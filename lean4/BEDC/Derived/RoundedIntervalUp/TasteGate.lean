import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RoundedIntervalUp : Type where
  | mk (Q S R D L U O E H C P N : BHist) : RoundedIntervalUp
  deriving DecidableEq

namespace RoundedIntervalUp

def roundedIntervalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: roundedIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: roundedIntervalEncodeBHist h

def roundedIntervalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (roundedIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (roundedIntervalDecodeBHist tail)

private theorem RoundedIntervalTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, roundedIntervalDecodeBHist (roundedIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def roundedIntervalFields : RoundedIntervalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RoundedIntervalUp.mk Q S R D L U O E H C P N => [Q, S, R, D, L, U, O, E, H, C, P, N]

def roundedIntervalToEventFlow : RoundedIntervalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (roundedIntervalFields x).map roundedIntervalEncodeBHist

private def roundedIntervalEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => roundedIntervalEventAt index rest

def roundedIntervalFromEventFlow (ef : EventFlow) : Option RoundedIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RoundedIntervalUp.mk
      (roundedIntervalDecodeBHist (roundedIntervalEventAt 0 ef))
      (roundedIntervalDecodeBHist (roundedIntervalEventAt 1 ef))
      (roundedIntervalDecodeBHist (roundedIntervalEventAt 2 ef))
      (roundedIntervalDecodeBHist (roundedIntervalEventAt 3 ef))
      (roundedIntervalDecodeBHist (roundedIntervalEventAt 4 ef))
      (roundedIntervalDecodeBHist (roundedIntervalEventAt 5 ef))
      (roundedIntervalDecodeBHist (roundedIntervalEventAt 6 ef))
      (roundedIntervalDecodeBHist (roundedIntervalEventAt 7 ef))
      (roundedIntervalDecodeBHist (roundedIntervalEventAt 8 ef))
      (roundedIntervalDecodeBHist (roundedIntervalEventAt 9 ef))
      (roundedIntervalDecodeBHist (roundedIntervalEventAt 10 ef))
      (roundedIntervalDecodeBHist (roundedIntervalEventAt 11 ef)))

private theorem RoundedIntervalTasteGate_single_carrier_alignment_round_trip
    (x : RoundedIntervalUp) :
    roundedIntervalFromEventFlow (roundedIntervalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk Q S R D L U O E H C P N =>
      change
        some
          (RoundedIntervalUp.mk
            (roundedIntervalDecodeBHist (roundedIntervalEncodeBHist Q))
            (roundedIntervalDecodeBHist (roundedIntervalEncodeBHist S))
            (roundedIntervalDecodeBHist (roundedIntervalEncodeBHist R))
            (roundedIntervalDecodeBHist (roundedIntervalEncodeBHist D))
            (roundedIntervalDecodeBHist (roundedIntervalEncodeBHist L))
            (roundedIntervalDecodeBHist (roundedIntervalEncodeBHist U))
            (roundedIntervalDecodeBHist (roundedIntervalEncodeBHist O))
            (roundedIntervalDecodeBHist (roundedIntervalEncodeBHist E))
            (roundedIntervalDecodeBHist (roundedIntervalEncodeBHist H))
            (roundedIntervalDecodeBHist (roundedIntervalEncodeBHist C))
            (roundedIntervalDecodeBHist (roundedIntervalEncodeBHist P))
            (roundedIntervalDecodeBHist (roundedIntervalEncodeBHist N))) =
          some (RoundedIntervalUp.mk Q S R D L U O E H C P N)
      rw [RoundedIntervalTasteGate_single_carrier_alignment_decode_encode Q,
        RoundedIntervalTasteGate_single_carrier_alignment_decode_encode S,
        RoundedIntervalTasteGate_single_carrier_alignment_decode_encode R,
        RoundedIntervalTasteGate_single_carrier_alignment_decode_encode D,
        RoundedIntervalTasteGate_single_carrier_alignment_decode_encode L,
        RoundedIntervalTasteGate_single_carrier_alignment_decode_encode U,
        RoundedIntervalTasteGate_single_carrier_alignment_decode_encode O,
        RoundedIntervalTasteGate_single_carrier_alignment_decode_encode E,
        RoundedIntervalTasteGate_single_carrier_alignment_decode_encode H,
        RoundedIntervalTasteGate_single_carrier_alignment_decode_encode C,
        RoundedIntervalTasteGate_single_carrier_alignment_decode_encode P,
        RoundedIntervalTasteGate_single_carrier_alignment_decode_encode N]

private theorem RoundedIntervalTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RoundedIntervalUp} :
    roundedIntervalToEventFlow x = roundedIntervalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      roundedIntervalFromEventFlow (roundedIntervalToEventFlow x) =
        roundedIntervalFromEventFlow (roundedIntervalToEventFlow y) :=
    congrArg roundedIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RoundedIntervalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RoundedIntervalTasteGate_single_carrier_alignment_round_trip y)))

private theorem RoundedIntervalTasteGate_single_carrier_alignment_fields :
    ∀ x y : RoundedIntervalUp, roundedIntervalFields x = roundedIntervalFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Q1 S1 R1 D1 L1 U1 O1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk Q2 S2 R2 D2 L2 U2 O2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance roundedIntervalBHistCarrier : BHistCarrier RoundedIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := roundedIntervalToEventFlow
  fromEventFlow := roundedIntervalFromEventFlow

instance roundedIntervalChapterTasteGate : ChapterTasteGate RoundedIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change roundedIntervalFromEventFlow (roundedIntervalToEventFlow x) = some x
    exact RoundedIntervalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RoundedIntervalTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance roundedIntervalFieldFaithful : FieldFaithful RoundedIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := roundedIntervalFields
  field_faithful := RoundedIntervalTasteGate_single_carrier_alignment_fields

instance roundedIntervalNontrivial : Nontrivial RoundedIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RoundedIntervalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RoundedIntervalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RoundedIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  roundedIntervalChapterTasteGate

theorem RoundedIntervalTasteGate_single_carrier_alignment :
    (∀ h : BHist, roundedIntervalDecodeBHist (roundedIntervalEncodeBHist h) = h) ∧
      (∀ x : RoundedIntervalUp,
        roundedIntervalFromEventFlow (roundedIntervalToEventFlow x) = some x) ∧
        (∀ x y : RoundedIntervalUp,
          roundedIntervalToEventFlow x = roundedIntervalToEventFlow y → x = y) ∧
          roundedIntervalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨RoundedIntervalTasteGate_single_carrier_alignment_decode_encode,
      RoundedIntervalTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => RoundedIntervalTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end RoundedIntervalUp

end BEDC.Derived
