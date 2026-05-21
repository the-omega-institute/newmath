import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTailEstimateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTailEstimateUp : Type where
  | mk (M W D R E H C P N : BHist) : RegularCauchyTailEstimateUp
  deriving DecidableEq

def regularCauchyTailEstimateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTailEstimateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTailEstimateEncodeBHist h

def regularCauchyTailEstimateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTailEstimateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTailEstimateDecodeBHist tail)

private theorem regularCauchyTailEstimate_decode_encode_bhist :
    ∀ h : BHist,
      regularCauchyTailEstimateDecodeBHist (regularCauchyTailEstimateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyTailEstimateFields : RegularCauchyTailEstimateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTailEstimateUp.mk M W D R E H C P N => [M, W, D, R, E, H, C, P, N]

def regularCauchyTailEstimateToEventFlow : RegularCauchyTailEstimateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTailEstimateUp.mk M W D R E H C P N =>
      [regularCauchyTailEstimateEncodeBHist M,
        regularCauchyTailEstimateEncodeBHist W,
        regularCauchyTailEstimateEncodeBHist D,
        regularCauchyTailEstimateEncodeBHist R,
        regularCauchyTailEstimateEncodeBHist E,
        regularCauchyTailEstimateEncodeBHist H,
        regularCauchyTailEstimateEncodeBHist C,
        regularCauchyTailEstimateEncodeBHist P,
        regularCauchyTailEstimateEncodeBHist N]

private def regularCauchyTailEstimateRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => regularCauchyTailEstimateRawAt n rest

private def regularCauchyTailEstimateLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => regularCauchyTailEstimateLengthEq n rest

def regularCauchyTailEstimateFromEventFlow : EventFlow → Option RegularCauchyTailEstimateUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match regularCauchyTailEstimateLengthEq 9 flow with
      | true =>
          some
            (RegularCauchyTailEstimateUp.mk
              (regularCauchyTailEstimateDecodeBHist
                (regularCauchyTailEstimateRawAt 0 flow))
              (regularCauchyTailEstimateDecodeBHist
                (regularCauchyTailEstimateRawAt 1 flow))
              (regularCauchyTailEstimateDecodeBHist
                (regularCauchyTailEstimateRawAt 2 flow))
              (regularCauchyTailEstimateDecodeBHist
                (regularCauchyTailEstimateRawAt 3 flow))
              (regularCauchyTailEstimateDecodeBHist
                (regularCauchyTailEstimateRawAt 4 flow))
              (regularCauchyTailEstimateDecodeBHist
                (regularCauchyTailEstimateRawAt 5 flow))
              (regularCauchyTailEstimateDecodeBHist
                (regularCauchyTailEstimateRawAt 6 flow))
              (regularCauchyTailEstimateDecodeBHist
                (regularCauchyTailEstimateRawAt 7 flow))
              (regularCauchyTailEstimateDecodeBHist
                (regularCauchyTailEstimateRawAt 8 flow)))
      | false => none

private theorem regularCauchyTailEstimate_round_trip :
    ∀ x : RegularCauchyTailEstimateUp,
      regularCauchyTailEstimateFromEventFlow (regularCauchyTailEstimateToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M W D R E H C P N =>
      change
        some
          (RegularCauchyTailEstimateUp.mk
            (regularCauchyTailEstimateDecodeBHist
              (regularCauchyTailEstimateEncodeBHist M))
            (regularCauchyTailEstimateDecodeBHist
              (regularCauchyTailEstimateEncodeBHist W))
            (regularCauchyTailEstimateDecodeBHist
              (regularCauchyTailEstimateEncodeBHist D))
            (regularCauchyTailEstimateDecodeBHist
              (regularCauchyTailEstimateEncodeBHist R))
            (regularCauchyTailEstimateDecodeBHist
              (regularCauchyTailEstimateEncodeBHist E))
            (regularCauchyTailEstimateDecodeBHist
              (regularCauchyTailEstimateEncodeBHist H))
            (regularCauchyTailEstimateDecodeBHist
              (regularCauchyTailEstimateEncodeBHist C))
            (regularCauchyTailEstimateDecodeBHist
              (regularCauchyTailEstimateEncodeBHist P))
            (regularCauchyTailEstimateDecodeBHist
              (regularCauchyTailEstimateEncodeBHist N))) =
          some (RegularCauchyTailEstimateUp.mk M W D R E H C P N)
      rw [regularCauchyTailEstimate_decode_encode_bhist M,
        regularCauchyTailEstimate_decode_encode_bhist W,
        regularCauchyTailEstimate_decode_encode_bhist D,
        regularCauchyTailEstimate_decode_encode_bhist R,
        regularCauchyTailEstimate_decode_encode_bhist E,
        regularCauchyTailEstimate_decode_encode_bhist H,
        regularCauchyTailEstimate_decode_encode_bhist C,
        regularCauchyTailEstimate_decode_encode_bhist P,
        regularCauchyTailEstimate_decode_encode_bhist N]

private theorem regularCauchyTailEstimateToEventFlow_injective
    {x y : RegularCauchyTailEstimateUp} :
    regularCauchyTailEstimateToEventFlow x =
        regularCauchyTailEstimateToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTailEstimateFromEventFlow (regularCauchyTailEstimateToEventFlow x) =
        regularCauchyTailEstimateFromEventFlow (regularCauchyTailEstimateToEventFlow y) :=
    congrArg regularCauchyTailEstimateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyTailEstimate_round_trip x).symm
      (Eq.trans hread (regularCauchyTailEstimate_round_trip y)))

private theorem regularCauchyTailEstimate_field_faithful :
    ∀ x y : RegularCauchyTailEstimateUp,
      regularCauchyTailEstimateFields x = regularCauchyTailEstimateFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk M1 W1 D1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 W2 D2 R2 E2 H2 C2 P2 N2 =>
          cases h
          rfl

instance regularCauchyTailEstimateBHistCarrier :
    BHistCarrier RegularCauchyTailEstimateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTailEstimateToEventFlow
  fromEventFlow := regularCauchyTailEstimateFromEventFlow

instance regularCauchyTailEstimateChapterTasteGate :
    ChapterTasteGate RegularCauchyTailEstimateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyTailEstimateFromEventFlow (regularCauchyTailEstimateToEventFlow x) =
        some x
    exact regularCauchyTailEstimate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyTailEstimateToEventFlow_injective heq)

instance regularCauchyTailEstimateFieldFaithful :
    FieldFaithful RegularCauchyTailEstimateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyTailEstimateFields
  field_faithful := regularCauchyTailEstimate_field_faithful

instance regularCauchyTailEstimateNontrivial : Nontrivial RegularCauchyTailEstimateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyTailEstimateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyTailEstimateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyTailEstimateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyTailEstimateChapterTasteGate

theorem RegularCauchyTailEstimateTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyTailEstimateDecodeBHist (regularCauchyTailEstimateEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyTailEstimateUp,
        regularCauchyTailEstimateFromEventFlow
          (regularCauchyTailEstimateToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyTailEstimateUp,
          regularCauchyTailEstimateToEventFlow x =
            regularCauchyTailEstimateToEventFlow y → x = y) ∧
          regularCauchyTailEstimateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨regularCauchyTailEstimate_decode_encode_bhist,
      regularCauchyTailEstimate_round_trip,
      by
        intro x y heq
        exact regularCauchyTailEstimateToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RegularCauchyTailEstimateUp
