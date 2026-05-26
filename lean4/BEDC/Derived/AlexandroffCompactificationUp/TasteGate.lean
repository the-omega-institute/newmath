import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AlexandroffCompactificationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AlexandroffCompactificationUp : Type where
  | mk (X T L S infinity O K H C P N : BHist) : AlexandroffCompactificationUp
  deriving DecidableEq

def alexandroffCompactificationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: alexandroffCompactificationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: alexandroffCompactificationEncodeBHist h

def alexandroffCompactificationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (alexandroffCompactificationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (alexandroffCompactificationDecodeBHist tail)

private theorem alexandroffCompactification_decode_encode_bhist :
    ∀ h : BHist, alexandroffCompactificationDecodeBHist
      (alexandroffCompactificationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def alexandroffCompactificationFields :
    AlexandroffCompactificationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AlexandroffCompactificationUp.mk X T L S infinity O K H C P N =>
      [X, T, L, S, infinity, O, K, H, C, P, N]

def alexandroffCompactificationToEventFlow :
    AlexandroffCompactificationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AlexandroffCompactificationUp.mk X T L S infinity O K H C P N =>
      [alexandroffCompactificationEncodeBHist X,
        alexandroffCompactificationEncodeBHist T,
        alexandroffCompactificationEncodeBHist L,
        alexandroffCompactificationEncodeBHist S,
        alexandroffCompactificationEncodeBHist infinity,
        alexandroffCompactificationEncodeBHist O,
        alexandroffCompactificationEncodeBHist K,
        alexandroffCompactificationEncodeBHist H,
        alexandroffCompactificationEncodeBHist C,
        alexandroffCompactificationEncodeBHist P,
        alexandroffCompactificationEncodeBHist N]

private def alexandroffCompactificationRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => alexandroffCompactificationRawAt n rest

private def alexandroffCompactificationLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => alexandroffCompactificationLengthEq n rest

def alexandroffCompactificationFromEventFlow :
    EventFlow → Option AlexandroffCompactificationUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match alexandroffCompactificationLengthEq 11 flow with
      | true =>
          some
            (AlexandroffCompactificationUp.mk
              (alexandroffCompactificationDecodeBHist
                (alexandroffCompactificationRawAt 0 flow))
              (alexandroffCompactificationDecodeBHist
                (alexandroffCompactificationRawAt 1 flow))
              (alexandroffCompactificationDecodeBHist
                (alexandroffCompactificationRawAt 2 flow))
              (alexandroffCompactificationDecodeBHist
                (alexandroffCompactificationRawAt 3 flow))
              (alexandroffCompactificationDecodeBHist
                (alexandroffCompactificationRawAt 4 flow))
              (alexandroffCompactificationDecodeBHist
                (alexandroffCompactificationRawAt 5 flow))
              (alexandroffCompactificationDecodeBHist
                (alexandroffCompactificationRawAt 6 flow))
              (alexandroffCompactificationDecodeBHist
                (alexandroffCompactificationRawAt 7 flow))
              (alexandroffCompactificationDecodeBHist
                (alexandroffCompactificationRawAt 8 flow))
              (alexandroffCompactificationDecodeBHist
                (alexandroffCompactificationRawAt 9 flow))
              (alexandroffCompactificationDecodeBHist
                (alexandroffCompactificationRawAt 10 flow)))
      | false => none

private theorem alexandroffCompactification_round_trip :
    ∀ x : AlexandroffCompactificationUp,
      alexandroffCompactificationFromEventFlow
        (alexandroffCompactificationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X T L S infinity O K H C P N =>
      change
        some
          (AlexandroffCompactificationUp.mk
            (alexandroffCompactificationDecodeBHist
              (alexandroffCompactificationEncodeBHist X))
            (alexandroffCompactificationDecodeBHist
              (alexandroffCompactificationEncodeBHist T))
            (alexandroffCompactificationDecodeBHist
              (alexandroffCompactificationEncodeBHist L))
            (alexandroffCompactificationDecodeBHist
              (alexandroffCompactificationEncodeBHist S))
            (alexandroffCompactificationDecodeBHist
              (alexandroffCompactificationEncodeBHist infinity))
            (alexandroffCompactificationDecodeBHist
              (alexandroffCompactificationEncodeBHist O))
            (alexandroffCompactificationDecodeBHist
              (alexandroffCompactificationEncodeBHist K))
            (alexandroffCompactificationDecodeBHist
              (alexandroffCompactificationEncodeBHist H))
            (alexandroffCompactificationDecodeBHist
              (alexandroffCompactificationEncodeBHist C))
            (alexandroffCompactificationDecodeBHist
              (alexandroffCompactificationEncodeBHist P))
            (alexandroffCompactificationDecodeBHist
              (alexandroffCompactificationEncodeBHist N))) =
          some (AlexandroffCompactificationUp.mk X T L S infinity O K H C P N)
      rw [alexandroffCompactification_decode_encode_bhist X,
        alexandroffCompactification_decode_encode_bhist T,
        alexandroffCompactification_decode_encode_bhist L,
        alexandroffCompactification_decode_encode_bhist S,
        alexandroffCompactification_decode_encode_bhist infinity,
        alexandroffCompactification_decode_encode_bhist O,
        alexandroffCompactification_decode_encode_bhist K,
        alexandroffCompactification_decode_encode_bhist H,
        alexandroffCompactification_decode_encode_bhist C,
        alexandroffCompactification_decode_encode_bhist P,
        alexandroffCompactification_decode_encode_bhist N]

private theorem alexandroffCompactificationToEventFlow_injective
    {x y : AlexandroffCompactificationUp} :
    alexandroffCompactificationToEventFlow x =
        alexandroffCompactificationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      alexandroffCompactificationFromEventFlow
          (alexandroffCompactificationToEventFlow x) =
        alexandroffCompactificationFromEventFlow
          (alexandroffCompactificationToEventFlow y) :=
    congrArg alexandroffCompactificationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (alexandroffCompactification_round_trip x).symm
      (Eq.trans hread (alexandroffCompactification_round_trip y)))

instance alexandroffCompactificationBHistCarrier :
    BHistCarrier AlexandroffCompactificationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := alexandroffCompactificationToEventFlow
  fromEventFlow := alexandroffCompactificationFromEventFlow

instance alexandroffCompactificationChapterTasteGate :
    ChapterTasteGate AlexandroffCompactificationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change alexandroffCompactificationFromEventFlow
      (alexandroffCompactificationToEventFlow x) = some x
    exact alexandroffCompactification_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (alexandroffCompactificationToEventFlow_injective heq)

def taste_gate : ChapterTasteGate AlexandroffCompactificationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  alexandroffCompactificationChapterTasteGate

theorem AlexandroffCompactificationTasteGate_single_carrier_alignment :
    (∀ h : BHist, alexandroffCompactificationDecodeBHist
      (alexandroffCompactificationEncodeBHist h) = h) ∧
      alexandroffCompactificationFields
          (AlexandroffCompactificationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨alexandroffCompactification_decode_encode_bhist, rfl⟩

end BEDC.Derived.AlexandroffCompactificationUp
