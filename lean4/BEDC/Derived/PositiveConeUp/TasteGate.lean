import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PositiveConeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PositiveConeUp : Type where
  | mk (R P A D W Q H C K N : BHist) : PositiveConeUp
  deriving DecidableEq

def positiveConeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: positiveConeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: positiveConeEncodeBHist h

def positiveConeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (positiveConeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (positiveConeDecodeBHist tail)

private theorem PositiveConeTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, positiveConeDecodeBHist (positiveConeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def positiveConeFields : PositiveConeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PositiveConeUp.mk R P A D W Q H C K N => [R, P, A, D, W, Q, H, C, K, N]

def positiveConeToEventFlow : PositiveConeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PositiveConeUp.mk R P A D W Q H C K N =>
      [[BMark.b0],
        positiveConeEncodeBHist R,
        [BMark.b1, BMark.b0],
        positiveConeEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b0],
        positiveConeEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        positiveConeEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        positiveConeEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        positiveConeEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        positiveConeEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        positiveConeEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        positiveConeEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        positiveConeEncodeBHist N]

private def positiveConeRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => positiveConeRawAt n rest

private def positiveConeLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => positiveConeLengthEq n rest

def positiveConeFromEventFlow : EventFlow → Option PositiveConeUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match positiveConeLengthEq 20 flow with
      | true =>
          some
            (PositiveConeUp.mk
              (positiveConeDecodeBHist (positiveConeRawAt 1 flow))
              (positiveConeDecodeBHist (positiveConeRawAt 3 flow))
              (positiveConeDecodeBHist (positiveConeRawAt 5 flow))
              (positiveConeDecodeBHist (positiveConeRawAt 7 flow))
              (positiveConeDecodeBHist (positiveConeRawAt 9 flow))
              (positiveConeDecodeBHist (positiveConeRawAt 11 flow))
              (positiveConeDecodeBHist (positiveConeRawAt 13 flow))
              (positiveConeDecodeBHist (positiveConeRawAt 15 flow))
              (positiveConeDecodeBHist (positiveConeRawAt 17 flow))
              (positiveConeDecodeBHist (positiveConeRawAt 19 flow)))
      | false => none

private theorem PositiveConeTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PositiveConeUp,
      positiveConeFromEventFlow (positiveConeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R P A D W Q H C K N =>
      change
        some
          (PositiveConeUp.mk
            (positiveConeDecodeBHist (positiveConeEncodeBHist R))
            (positiveConeDecodeBHist (positiveConeEncodeBHist P))
            (positiveConeDecodeBHist (positiveConeEncodeBHist A))
            (positiveConeDecodeBHist (positiveConeEncodeBHist D))
            (positiveConeDecodeBHist (positiveConeEncodeBHist W))
            (positiveConeDecodeBHist (positiveConeEncodeBHist Q))
            (positiveConeDecodeBHist (positiveConeEncodeBHist H))
            (positiveConeDecodeBHist (positiveConeEncodeBHist C))
            (positiveConeDecodeBHist (positiveConeEncodeBHist K))
            (positiveConeDecodeBHist (positiveConeEncodeBHist N))) =
          some (PositiveConeUp.mk R P A D W Q H C K N)
      rw [PositiveConeTasteGate_single_carrier_alignment_decode_encode R,
        PositiveConeTasteGate_single_carrier_alignment_decode_encode P,
        PositiveConeTasteGate_single_carrier_alignment_decode_encode A,
        PositiveConeTasteGate_single_carrier_alignment_decode_encode D,
        PositiveConeTasteGate_single_carrier_alignment_decode_encode W,
        PositiveConeTasteGate_single_carrier_alignment_decode_encode Q,
        PositiveConeTasteGate_single_carrier_alignment_decode_encode H,
        PositiveConeTasteGate_single_carrier_alignment_decode_encode C,
        PositiveConeTasteGate_single_carrier_alignment_decode_encode K,
        PositiveConeTasteGate_single_carrier_alignment_decode_encode N]

private theorem PositiveConeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PositiveConeUp} :
    positiveConeToEventFlow x = positiveConeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      positiveConeFromEventFlow (positiveConeToEventFlow x) =
        positiveConeFromEventFlow (positiveConeToEventFlow y) :=
    congrArg positiveConeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PositiveConeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PositiveConeTasteGate_single_carrier_alignment_round_trip y)))

private theorem PositiveConeTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : PositiveConeUp, positiveConeFields x = positiveConeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R1 P1 A1 D1 W1 Q1 H1 C1 K1 N1 =>
      cases y with
      | mk R2 P2 A2 D2 W2 Q2 H2 C2 K2 N2 =>
          cases hfields
          rfl

instance positiveConeBHistCarrier : BHistCarrier PositiveConeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := positiveConeToEventFlow
  fromEventFlow := positiveConeFromEventFlow

instance positiveConeChapterTasteGate : ChapterTasteGate PositiveConeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change positiveConeFromEventFlow (positiveConeToEventFlow x) = some x
    exact PositiveConeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PositiveConeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance positiveConeFieldFaithful : FieldFaithful PositiveConeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := positiveConeFields
  field_faithful := PositiveConeTasteGate_single_carrier_alignment_fields_faithful

instance positiveConeNontrivial : Nontrivial PositiveConeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PositiveConeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PositiveConeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PositiveConeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  positiveConeChapterTasteGate

theorem PositiveConeTasteGate_single_carrier_alignment :
    (∀ h : BHist, positiveConeDecodeBHist (positiveConeEncodeBHist h) = h) ∧
      (∀ x : PositiveConeUp,
        positiveConeFromEventFlow (positiveConeToEventFlow x) = some x) ∧
        (∀ x y : PositiveConeUp,
          positiveConeToEventFlow x = positiveConeToEventFlow y → x = y) ∧
          positiveConeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨PositiveConeTasteGate_single_carrier_alignment_decode_encode,
      PositiveConeTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => PositiveConeTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.PositiveConeUp
