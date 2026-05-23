import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FastRegularCauchyEquivalenceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FastRegularCauchyEquivalenceUp : Type where
  | mk (F S D Q E H C P N : BHist) : FastRegularCauchyEquivalenceUp
  deriving DecidableEq

def fastRegularCauchyEquivalenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fastRegularCauchyEquivalenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fastRegularCauchyEquivalenceEncodeBHist h

def fastRegularCauchyEquivalenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fastRegularCauchyEquivalenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fastRegularCauchyEquivalenceDecodeBHist tail)

private theorem fastRegularCauchyEquivalence_decode_encode_bhist :
    ∀ h : BHist,
      fastRegularCauchyEquivalenceDecodeBHist
          (fastRegularCauchyEquivalenceEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def fastRegularCauchyEquivalenceFields :
    FastRegularCauchyEquivalenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FastRegularCauchyEquivalenceUp.mk F S D Q E H C P N => [F, S, D, Q, E, H, C, P, N]

def fastRegularCauchyEquivalenceToEventFlow :
    FastRegularCauchyEquivalenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (fastRegularCauchyEquivalenceFields x).map fastRegularCauchyEquivalenceEncodeBHist

private def fastRegularCauchyEquivalenceRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => fastRegularCauchyEquivalenceRawAt n rest

private def fastRegularCauchyEquivalenceLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => fastRegularCauchyEquivalenceLengthEq n rest

def fastRegularCauchyEquivalenceFromEventFlow :
    EventFlow → Option FastRegularCauchyEquivalenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match fastRegularCauchyEquivalenceLengthEq 9 flow with
      | true =>
          some
            (FastRegularCauchyEquivalenceUp.mk
              (fastRegularCauchyEquivalenceDecodeBHist
                (fastRegularCauchyEquivalenceRawAt 0 flow))
              (fastRegularCauchyEquivalenceDecodeBHist
                (fastRegularCauchyEquivalenceRawAt 1 flow))
              (fastRegularCauchyEquivalenceDecodeBHist
                (fastRegularCauchyEquivalenceRawAt 2 flow))
              (fastRegularCauchyEquivalenceDecodeBHist
                (fastRegularCauchyEquivalenceRawAt 3 flow))
              (fastRegularCauchyEquivalenceDecodeBHist
                (fastRegularCauchyEquivalenceRawAt 4 flow))
              (fastRegularCauchyEquivalenceDecodeBHist
                (fastRegularCauchyEquivalenceRawAt 5 flow))
              (fastRegularCauchyEquivalenceDecodeBHist
                (fastRegularCauchyEquivalenceRawAt 6 flow))
              (fastRegularCauchyEquivalenceDecodeBHist
                (fastRegularCauchyEquivalenceRawAt 7 flow))
              (fastRegularCauchyEquivalenceDecodeBHist
                (fastRegularCauchyEquivalenceRawAt 8 flow)))
      | false => none

private theorem fastRegularCauchyEquivalence_round_trip :
    ∀ x : FastRegularCauchyEquivalenceUp,
      fastRegularCauchyEquivalenceFromEventFlow
          (fastRegularCauchyEquivalenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F S D Q E H C P N =>
      change
        some
          (FastRegularCauchyEquivalenceUp.mk
            (fastRegularCauchyEquivalenceDecodeBHist
              (fastRegularCauchyEquivalenceEncodeBHist F))
            (fastRegularCauchyEquivalenceDecodeBHist
              (fastRegularCauchyEquivalenceEncodeBHist S))
            (fastRegularCauchyEquivalenceDecodeBHist
              (fastRegularCauchyEquivalenceEncodeBHist D))
            (fastRegularCauchyEquivalenceDecodeBHist
              (fastRegularCauchyEquivalenceEncodeBHist Q))
            (fastRegularCauchyEquivalenceDecodeBHist
              (fastRegularCauchyEquivalenceEncodeBHist E))
            (fastRegularCauchyEquivalenceDecodeBHist
              (fastRegularCauchyEquivalenceEncodeBHist H))
            (fastRegularCauchyEquivalenceDecodeBHist
              (fastRegularCauchyEquivalenceEncodeBHist C))
            (fastRegularCauchyEquivalenceDecodeBHist
              (fastRegularCauchyEquivalenceEncodeBHist P))
            (fastRegularCauchyEquivalenceDecodeBHist
              (fastRegularCauchyEquivalenceEncodeBHist N))) =
          some (FastRegularCauchyEquivalenceUp.mk F S D Q E H C P N)
      rw [fastRegularCauchyEquivalence_decode_encode_bhist F,
        fastRegularCauchyEquivalence_decode_encode_bhist S,
        fastRegularCauchyEquivalence_decode_encode_bhist D,
        fastRegularCauchyEquivalence_decode_encode_bhist Q,
        fastRegularCauchyEquivalence_decode_encode_bhist E,
        fastRegularCauchyEquivalence_decode_encode_bhist H,
        fastRegularCauchyEquivalence_decode_encode_bhist C,
        fastRegularCauchyEquivalence_decode_encode_bhist P,
        fastRegularCauchyEquivalence_decode_encode_bhist N]

private theorem fastRegularCauchyEquivalenceToEventFlow_injective
    {x y : FastRegularCauchyEquivalenceUp} :
    fastRegularCauchyEquivalenceToEventFlow x =
        fastRegularCauchyEquivalenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fastRegularCauchyEquivalenceFromEventFlow
          (fastRegularCauchyEquivalenceToEventFlow x) =
        fastRegularCauchyEquivalenceFromEventFlow
          (fastRegularCauchyEquivalenceToEventFlow y) :=
    congrArg fastRegularCauchyEquivalenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (fastRegularCauchyEquivalence_round_trip x).symm
      (Eq.trans hread (fastRegularCauchyEquivalence_round_trip y)))

private theorem fastRegularCauchyEquivalence_field_faithful :
    ∀ x y : FastRegularCauchyEquivalenceUp,
      fastRegularCauchyEquivalenceFields x = fastRegularCauchyEquivalenceFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 S1 D1 Q1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk F2 S2 D2 Q2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance fastRegularCauchyEquivalenceBHistCarrier :
    BHistCarrier FastRegularCauchyEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fastRegularCauchyEquivalenceToEventFlow
  fromEventFlow := fastRegularCauchyEquivalenceFromEventFlow

instance fastRegularCauchyEquivalenceChapterTasteGate :
    ChapterTasteGate FastRegularCauchyEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      fastRegularCauchyEquivalenceFromEventFlow
          (fastRegularCauchyEquivalenceToEventFlow x) =
        some x
    exact fastRegularCauchyEquivalence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fastRegularCauchyEquivalenceToEventFlow_injective heq)

instance fastRegularCauchyEquivalenceFieldFaithful :
    FieldFaithful FastRegularCauchyEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fastRegularCauchyEquivalenceFields
  field_faithful := fastRegularCauchyEquivalence_field_faithful

instance fastRegularCauchyEquivalenceNontrivial :
    Nontrivial FastRegularCauchyEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FastRegularCauchyEquivalenceUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FastRegularCauchyEquivalenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FastRegularCauchyEquivalenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fastRegularCauchyEquivalenceChapterTasteGate

theorem FastRegularCauchyEquivalenceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FastRegularCauchyEquivalenceUp) ∧
      Nonempty (FieldFaithful FastRegularCauchyEquivalenceUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial FastRegularCauchyEquivalenceUp) ∧
      (∀ h : BHist,
        fastRegularCauchyEquivalenceDecodeBHist
            (fastRegularCauchyEquivalenceEncodeBHist h) =
          h) ∧
      (∀ x : FastRegularCauchyEquivalenceUp,
        fastRegularCauchyEquivalenceFromEventFlow
            (fastRegularCauchyEquivalenceToEventFlow x) =
          some x) ∧
      (∀ x y : FastRegularCauchyEquivalenceUp,
        fastRegularCauchyEquivalenceToEventFlow x =
            fastRegularCauchyEquivalenceToEventFlow y →
          x = y) ∧
      fastRegularCauchyEquivalenceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨Nonempty.intro fastRegularCauchyEquivalenceChapterTasteGate,
      Nonempty.intro fastRegularCauchyEquivalenceFieldFaithful,
      Nonempty.intro fastRegularCauchyEquivalenceNontrivial,
      fastRegularCauchyEquivalence_decode_encode_bhist,
      fastRegularCauchyEquivalence_round_trip,
      (fun _ _ heq => fastRegularCauchyEquivalenceToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FastRegularCauchyEquivalenceUp.TasteGate
