import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NestedIntervalDiameterZeroUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NestedIntervalDiameterZeroUp : Type where
  | mk (I J D R E H C P N : BHist) : NestedIntervalDiameterZeroUp
  deriving DecidableEq

def nestedIntervalDiameterZeroEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nestedIntervalDiameterZeroEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nestedIntervalDiameterZeroEncodeBHist h

def nestedIntervalDiameterZeroDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nestedIntervalDiameterZeroDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nestedIntervalDiameterZeroDecodeBHist tail)

private theorem NestedIntervalDiameterZeroTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      nestedIntervalDiameterZeroDecodeBHist
        (nestedIntervalDiameterZeroEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def nestedIntervalDiameterZeroFields : NestedIntervalDiameterZeroUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NestedIntervalDiameterZeroUp.mk I J D R E H C P N => [I, J, D, R, E, H, C, P, N]

def nestedIntervalDiameterZeroToEventFlow : NestedIntervalDiameterZeroUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | NestedIntervalDiameterZeroUp.mk I J D R E H C P N =>
      [[BMark.b0],
        nestedIntervalDiameterZeroEncodeBHist I,
        [BMark.b1, BMark.b0],
        nestedIntervalDiameterZeroEncodeBHist J,
        [BMark.b1, BMark.b1, BMark.b0],
        nestedIntervalDiameterZeroEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        nestedIntervalDiameterZeroEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        nestedIntervalDiameterZeroEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        nestedIntervalDiameterZeroEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        nestedIntervalDiameterZeroEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        nestedIntervalDiameterZeroEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        nestedIntervalDiameterZeroEncodeBHist N]

private def nestedIntervalDiameterZeroRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => nestedIntervalDiameterZeroRawAt n rest

private def nestedIntervalDiameterZeroLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => nestedIntervalDiameterZeroLengthEq n rest

def nestedIntervalDiameterZeroFromEventFlow :
    EventFlow → Option NestedIntervalDiameterZeroUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match nestedIntervalDiameterZeroLengthEq 18 flow with
      | true =>
          some
            (NestedIntervalDiameterZeroUp.mk
              (nestedIntervalDiameterZeroDecodeBHist
                (nestedIntervalDiameterZeroRawAt 1 flow))
              (nestedIntervalDiameterZeroDecodeBHist
                (nestedIntervalDiameterZeroRawAt 3 flow))
              (nestedIntervalDiameterZeroDecodeBHist
                (nestedIntervalDiameterZeroRawAt 5 flow))
              (nestedIntervalDiameterZeroDecodeBHist
                (nestedIntervalDiameterZeroRawAt 7 flow))
              (nestedIntervalDiameterZeroDecodeBHist
                (nestedIntervalDiameterZeroRawAt 9 flow))
              (nestedIntervalDiameterZeroDecodeBHist
                (nestedIntervalDiameterZeroRawAt 11 flow))
              (nestedIntervalDiameterZeroDecodeBHist
                (nestedIntervalDiameterZeroRawAt 13 flow))
              (nestedIntervalDiameterZeroDecodeBHist
                (nestedIntervalDiameterZeroRawAt 15 flow))
              (nestedIntervalDiameterZeroDecodeBHist
                (nestedIntervalDiameterZeroRawAt 17 flow)))
      | false => none

private theorem NestedIntervalDiameterZeroTasteGate_single_carrier_alignment_round_trip :
    ∀ x : NestedIntervalDiameterZeroUp,
      nestedIntervalDiameterZeroFromEventFlow
        (nestedIntervalDiameterZeroToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I J D R E H C P N =>
      change
        some
          (NestedIntervalDiameterZeroUp.mk
            (nestedIntervalDiameterZeroDecodeBHist
              (nestedIntervalDiameterZeroEncodeBHist I))
            (nestedIntervalDiameterZeroDecodeBHist
              (nestedIntervalDiameterZeroEncodeBHist J))
            (nestedIntervalDiameterZeroDecodeBHist
              (nestedIntervalDiameterZeroEncodeBHist D))
            (nestedIntervalDiameterZeroDecodeBHist
              (nestedIntervalDiameterZeroEncodeBHist R))
            (nestedIntervalDiameterZeroDecodeBHist
              (nestedIntervalDiameterZeroEncodeBHist E))
            (nestedIntervalDiameterZeroDecodeBHist
              (nestedIntervalDiameterZeroEncodeBHist H))
            (nestedIntervalDiameterZeroDecodeBHist
              (nestedIntervalDiameterZeroEncodeBHist C))
            (nestedIntervalDiameterZeroDecodeBHist
              (nestedIntervalDiameterZeroEncodeBHist P))
            (nestedIntervalDiameterZeroDecodeBHist
              (nestedIntervalDiameterZeroEncodeBHist N))) =
          some (NestedIntervalDiameterZeroUp.mk I J D R E H C P N)
      rw [NestedIntervalDiameterZeroTasteGate_single_carrier_alignment_decode_encode I,
        NestedIntervalDiameterZeroTasteGate_single_carrier_alignment_decode_encode J,
        NestedIntervalDiameterZeroTasteGate_single_carrier_alignment_decode_encode D,
        NestedIntervalDiameterZeroTasteGate_single_carrier_alignment_decode_encode R,
        NestedIntervalDiameterZeroTasteGate_single_carrier_alignment_decode_encode E,
        NestedIntervalDiameterZeroTasteGate_single_carrier_alignment_decode_encode H,
        NestedIntervalDiameterZeroTasteGate_single_carrier_alignment_decode_encode C,
        NestedIntervalDiameterZeroTasteGate_single_carrier_alignment_decode_encode P,
        NestedIntervalDiameterZeroTasteGate_single_carrier_alignment_decode_encode N]

private theorem NestedIntervalDiameterZeroTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : NestedIntervalDiameterZeroUp} :
    nestedIntervalDiameterZeroToEventFlow x =
        nestedIntervalDiameterZeroToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      nestedIntervalDiameterZeroFromEventFlow
          (nestedIntervalDiameterZeroToEventFlow x) =
        nestedIntervalDiameterZeroFromEventFlow
          (nestedIntervalDiameterZeroToEventFlow y) :=
    congrArg nestedIntervalDiameterZeroFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (NestedIntervalDiameterZeroTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (NestedIntervalDiameterZeroTasteGate_single_carrier_alignment_round_trip y)))

private theorem NestedIntervalDiameterZeroTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : NestedIntervalDiameterZeroUp,
      nestedIntervalDiameterZeroFields x = nestedIntervalDiameterZeroFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 J1 D1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 J2 D2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance nestedIntervalDiameterZeroBHistCarrier :
    BHistCarrier NestedIntervalDiameterZeroUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nestedIntervalDiameterZeroToEventFlow
  fromEventFlow := nestedIntervalDiameterZeroFromEventFlow

instance nestedIntervalDiameterZeroChapterTasteGate :
    ChapterTasteGate NestedIntervalDiameterZeroUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      nestedIntervalDiameterZeroFromEventFlow
        (nestedIntervalDiameterZeroToEventFlow x) = some x
    exact NestedIntervalDiameterZeroTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (NestedIntervalDiameterZeroTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance nestedIntervalDiameterZeroFieldFaithful :
    FieldFaithful NestedIntervalDiameterZeroUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := nestedIntervalDiameterZeroFields
  field_faithful :=
    NestedIntervalDiameterZeroTasteGate_single_carrier_alignment_fields_faithful

instance nestedIntervalDiameterZeroNontrivial : Nontrivial NestedIntervalDiameterZeroUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨NestedIntervalDiameterZeroUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      NestedIntervalDiameterZeroUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate NestedIntervalDiameterZeroUp :=
  -- BEDC touchpoint anchor: BHist BMark
  nestedIntervalDiameterZeroChapterTasteGate

theorem NestedIntervalDiameterZeroTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      nestedIntervalDiameterZeroDecodeBHist
        (nestedIntervalDiameterZeroEncodeBHist h) = h) ∧
      (∀ x : NestedIntervalDiameterZeroUp,
        nestedIntervalDiameterZeroFromEventFlow
          (nestedIntervalDiameterZeroToEventFlow x) = some x) ∧
        (∀ x y : NestedIntervalDiameterZeroUp,
          nestedIntervalDiameterZeroToEventFlow x =
              nestedIntervalDiameterZeroToEventFlow y →
            x = y) ∧
          nestedIntervalDiameterZeroEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨NestedIntervalDiameterZeroTasteGate_single_carrier_alignment_decode_encode,
      NestedIntervalDiameterZeroTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        NestedIntervalDiameterZeroTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.NestedIntervalDiameterZeroUp
