import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KleeneRealizabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KleeneRealizabilityUp : Type where
  | mk (e I O T R H C P N : BHist) : KleeneRealizabilityUp
  deriving DecidableEq

def kleeneRealizabilityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kleeneRealizabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kleeneRealizabilityEncodeBHist h

def kleeneRealizabilityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kleeneRealizabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kleeneRealizabilityDecodeBHist tail)

private theorem kleeneRealizability_decode_encode :
    ∀ h : BHist, kleeneRealizabilityDecodeBHist
      (kleeneRealizabilityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kleeneRealizabilityFields : KleeneRealizabilityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KleeneRealizabilityUp.mk e I O T R H C P N => [e, I, O, T, R, H, C, P, N]

def kleeneRealizabilityToEventFlow : KleeneRealizabilityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (kleeneRealizabilityFields x).map kleeneRealizabilityEncodeBHist

private def kleeneRealizabilityRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => kleeneRealizabilityRawAt index rest

private def kleeneRealizabilityLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ index, _event :: rest => kleeneRealizabilityLengthEq index rest

def kleeneRealizabilityFromEventFlow : EventFlow → Option KleeneRealizabilityUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match kleeneRealizabilityLengthEq 9 flow with
      | true =>
          some
            (KleeneRealizabilityUp.mk
              (kleeneRealizabilityDecodeBHist (kleeneRealizabilityRawAt 0 flow))
              (kleeneRealizabilityDecodeBHist (kleeneRealizabilityRawAt 1 flow))
              (kleeneRealizabilityDecodeBHist (kleeneRealizabilityRawAt 2 flow))
              (kleeneRealizabilityDecodeBHist (kleeneRealizabilityRawAt 3 flow))
              (kleeneRealizabilityDecodeBHist (kleeneRealizabilityRawAt 4 flow))
              (kleeneRealizabilityDecodeBHist (kleeneRealizabilityRawAt 5 flow))
              (kleeneRealizabilityDecodeBHist (kleeneRealizabilityRawAt 6 flow))
              (kleeneRealizabilityDecodeBHist (kleeneRealizabilityRawAt 7 flow))
              (kleeneRealizabilityDecodeBHist (kleeneRealizabilityRawAt 8 flow)))
      | false => none

private theorem kleeneRealizability_round_trip :
    ∀ x : KleeneRealizabilityUp,
      kleeneRealizabilityFromEventFlow (kleeneRealizabilityToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk e I O T R H C P N =>
      change
        some
          (KleeneRealizabilityUp.mk
            (kleeneRealizabilityDecodeBHist (kleeneRealizabilityEncodeBHist e))
            (kleeneRealizabilityDecodeBHist (kleeneRealizabilityEncodeBHist I))
            (kleeneRealizabilityDecodeBHist (kleeneRealizabilityEncodeBHist O))
            (kleeneRealizabilityDecodeBHist (kleeneRealizabilityEncodeBHist T))
            (kleeneRealizabilityDecodeBHist (kleeneRealizabilityEncodeBHist R))
            (kleeneRealizabilityDecodeBHist (kleeneRealizabilityEncodeBHist H))
            (kleeneRealizabilityDecodeBHist (kleeneRealizabilityEncodeBHist C))
            (kleeneRealizabilityDecodeBHist (kleeneRealizabilityEncodeBHist P))
            (kleeneRealizabilityDecodeBHist (kleeneRealizabilityEncodeBHist N))) =
          some (KleeneRealizabilityUp.mk e I O T R H C P N)
      rw [kleeneRealizability_decode_encode e,
        kleeneRealizability_decode_encode I,
        kleeneRealizability_decode_encode O,
        kleeneRealizability_decode_encode T,
        kleeneRealizability_decode_encode R,
        kleeneRealizability_decode_encode H,
        kleeneRealizability_decode_encode C,
        kleeneRealizability_decode_encode P,
        kleeneRealizability_decode_encode N]

private theorem kleeneRealizabilityToEventFlow_injective
    {x y : KleeneRealizabilityUp} :
    kleeneRealizabilityToEventFlow x = kleeneRealizabilityToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kleeneRealizabilityFromEventFlow (kleeneRealizabilityToEventFlow x) =
        kleeneRealizabilityFromEventFlow (kleeneRealizabilityToEventFlow y) :=
    congrArg kleeneRealizabilityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (kleeneRealizability_round_trip x).symm
      (Eq.trans hread (kleeneRealizability_round_trip y)))

instance kleeneRealizabilityBHistCarrier :
    BHistCarrier KleeneRealizabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kleeneRealizabilityToEventFlow
  fromEventFlow := kleeneRealizabilityFromEventFlow

instance kleeneRealizabilityChapterTasteGate :
    ChapterTasteGate KleeneRealizabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      kleeneRealizabilityFromEventFlow (kleeneRealizabilityToEventFlow x) =
        some x
    exact kleeneRealizability_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (kleeneRealizabilityToEventFlow_injective heq)

theorem KleeneRealizabilityTasteGate_single_carrier_alignment :
    (∀ h : BHist, kleeneRealizabilityDecodeBHist
      (kleeneRealizabilityEncodeBHist h) = h) ∧
      (∀ x : KleeneRealizabilityUp,
        kleeneRealizabilityFromEventFlow
          (kleeneRealizabilityToEventFlow x) = some x) ∧
        (∀ x y : KleeneRealizabilityUp,
          kleeneRealizabilityToEventFlow x =
            kleeneRealizabilityToEventFlow y → x = y) ∧
          kleeneRealizabilityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact kleeneRealizability_decode_encode
  · constructor
    · exact kleeneRealizability_round_trip
    · constructor
      · intro x y heq
        exact kleeneRealizabilityToEventFlow_injective heq
      · rfl

end BEDC.Derived.KleeneRealizabilityUp
