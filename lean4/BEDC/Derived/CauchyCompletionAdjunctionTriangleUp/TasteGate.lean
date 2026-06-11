import BEDC.Derived.CauchyCompletionAdjunctionTriangleUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionAdjunctionTriangleUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def cauchyCompletionAdjunctionTriangleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionAdjunctionTriangleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionAdjunctionTriangleEncodeBHist h

def cauchyCompletionAdjunctionTriangleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionAdjunctionTriangleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionAdjunctionTriangleDecodeBHist tail)

private theorem cauchyCompletionAdjunctionTriangle_decode_encode_bhist :
    ∀ h : BHist,
      cauchyCompletionAdjunctionTriangleDecodeBHist
          (cauchyCompletionAdjunctionTriangleEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionAdjunctionTriangleToEventFlow :
    CauchyCompletionAdjunctionTriangleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (cauchyCompletionAdjunctionTriangleFields x).map
        cauchyCompletionAdjunctionTriangleEncodeBHist

private def cauchyCompletionAdjunctionTriangleRawAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => cauchyCompletionAdjunctionTriangleRawAt n rest

private def cauchyCompletionAdjunctionTriangleLengthEq :
    Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => cauchyCompletionAdjunctionTriangleLengthEq n rest

def cauchyCompletionAdjunctionTriangleFromEventFlow :
    EventFlow → Option CauchyCompletionAdjunctionTriangleUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match cauchyCompletionAdjunctionTriangleLengthEq 12 flow with
      | true =>
          some
            (CauchyCompletionAdjunctionTriangleUp.mk
              (cauchyCompletionAdjunctionTriangleDecodeBHist
                (cauchyCompletionAdjunctionTriangleRawAt 0 flow))
              (cauchyCompletionAdjunctionTriangleDecodeBHist
                (cauchyCompletionAdjunctionTriangleRawAt 1 flow))
              (cauchyCompletionAdjunctionTriangleDecodeBHist
                (cauchyCompletionAdjunctionTriangleRawAt 2 flow))
              (cauchyCompletionAdjunctionTriangleDecodeBHist
                (cauchyCompletionAdjunctionTriangleRawAt 3 flow))
              (cauchyCompletionAdjunctionTriangleDecodeBHist
                (cauchyCompletionAdjunctionTriangleRawAt 4 flow))
              (cauchyCompletionAdjunctionTriangleDecodeBHist
                (cauchyCompletionAdjunctionTriangleRawAt 5 flow))
              (cauchyCompletionAdjunctionTriangleDecodeBHist
                (cauchyCompletionAdjunctionTriangleRawAt 6 flow))
              (cauchyCompletionAdjunctionTriangleDecodeBHist
                (cauchyCompletionAdjunctionTriangleRawAt 7 flow))
              (cauchyCompletionAdjunctionTriangleDecodeBHist
                (cauchyCompletionAdjunctionTriangleRawAt 8 flow))
              (cauchyCompletionAdjunctionTriangleDecodeBHist
                (cauchyCompletionAdjunctionTriangleRawAt 9 flow))
              (cauchyCompletionAdjunctionTriangleDecodeBHist
                (cauchyCompletionAdjunctionTriangleRawAt 10 flow))
              (cauchyCompletionAdjunctionTriangleDecodeBHist
                (cauchyCompletionAdjunctionTriangleRawAt 11 flow)))
      | false => none

private theorem cauchyCompletionAdjunctionTriangle_round_trip :
    ∀ x : CauchyCompletionAdjunctionTriangleUp,
      cauchyCompletionAdjunctionTriangleFromEventFlow
          (cauchyCompletionAdjunctionTriangleToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F A U I R W D E H C P N =>
      change
        some
          (CauchyCompletionAdjunctionTriangleUp.mk
            (cauchyCompletionAdjunctionTriangleDecodeBHist
              (cauchyCompletionAdjunctionTriangleEncodeBHist F))
            (cauchyCompletionAdjunctionTriangleDecodeBHist
              (cauchyCompletionAdjunctionTriangleEncodeBHist A))
            (cauchyCompletionAdjunctionTriangleDecodeBHist
              (cauchyCompletionAdjunctionTriangleEncodeBHist U))
            (cauchyCompletionAdjunctionTriangleDecodeBHist
              (cauchyCompletionAdjunctionTriangleEncodeBHist I))
            (cauchyCompletionAdjunctionTriangleDecodeBHist
              (cauchyCompletionAdjunctionTriangleEncodeBHist R))
            (cauchyCompletionAdjunctionTriangleDecodeBHist
              (cauchyCompletionAdjunctionTriangleEncodeBHist W))
            (cauchyCompletionAdjunctionTriangleDecodeBHist
              (cauchyCompletionAdjunctionTriangleEncodeBHist D))
            (cauchyCompletionAdjunctionTriangleDecodeBHist
              (cauchyCompletionAdjunctionTriangleEncodeBHist E))
            (cauchyCompletionAdjunctionTriangleDecodeBHist
              (cauchyCompletionAdjunctionTriangleEncodeBHist H))
            (cauchyCompletionAdjunctionTriangleDecodeBHist
              (cauchyCompletionAdjunctionTriangleEncodeBHist C))
            (cauchyCompletionAdjunctionTriangleDecodeBHist
              (cauchyCompletionAdjunctionTriangleEncodeBHist P))
            (cauchyCompletionAdjunctionTriangleDecodeBHist
              (cauchyCompletionAdjunctionTriangleEncodeBHist N))) =
          some (CauchyCompletionAdjunctionTriangleUp.mk F A U I R W D E H C P N)
      rw [cauchyCompletionAdjunctionTriangle_decode_encode_bhist F,
        cauchyCompletionAdjunctionTriangle_decode_encode_bhist A,
        cauchyCompletionAdjunctionTriangle_decode_encode_bhist U,
        cauchyCompletionAdjunctionTriangle_decode_encode_bhist I,
        cauchyCompletionAdjunctionTriangle_decode_encode_bhist R,
        cauchyCompletionAdjunctionTriangle_decode_encode_bhist W,
        cauchyCompletionAdjunctionTriangle_decode_encode_bhist D,
        cauchyCompletionAdjunctionTriangle_decode_encode_bhist E,
        cauchyCompletionAdjunctionTriangle_decode_encode_bhist H,
        cauchyCompletionAdjunctionTriangle_decode_encode_bhist C,
        cauchyCompletionAdjunctionTriangle_decode_encode_bhist P,
        cauchyCompletionAdjunctionTriangle_decode_encode_bhist N]

private theorem cauchyCompletionAdjunctionTriangleToEventFlow_injective
    {x y : CauchyCompletionAdjunctionTriangleUp} :
    cauchyCompletionAdjunctionTriangleToEventFlow x =
        cauchyCompletionAdjunctionTriangleToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionAdjunctionTriangleFromEventFlow
          (cauchyCompletionAdjunctionTriangleToEventFlow x) =
        cauchyCompletionAdjunctionTriangleFromEventFlow
          (cauchyCompletionAdjunctionTriangleToEventFlow y) :=
    congrArg cauchyCompletionAdjunctionTriangleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyCompletionAdjunctionTriangle_round_trip x).symm
      (Eq.trans hread (cauchyCompletionAdjunctionTriangle_round_trip y)))

private theorem cauchyCompletionAdjunctionTriangle_field_faithful :
    ∀ x y : CauchyCompletionAdjunctionTriangleUp,
      cauchyCompletionAdjunctionTriangleFields x =
          cauchyCompletionAdjunctionTriangleFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 A1 U1 I1 R1 W1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk F2 A2 U2 I2 R2 W2 D2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchyCompletionAdjunctionTriangleBHistCarrier :
    BHistCarrier CauchyCompletionAdjunctionTriangleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionAdjunctionTriangleToEventFlow
  fromEventFlow := cauchyCompletionAdjunctionTriangleFromEventFlow

instance cauchyCompletionAdjunctionTriangleChapterTasteGate :
    ChapterTasteGate CauchyCompletionAdjunctionTriangleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionAdjunctionTriangleFromEventFlow
          (cauchyCompletionAdjunctionTriangleToEventFlow x) =
        some x
    exact cauchyCompletionAdjunctionTriangle_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCompletionAdjunctionTriangleToEventFlow_injective heq)

instance cauchyCompletionAdjunctionTriangleFieldFaithful :
    FieldFaithful CauchyCompletionAdjunctionTriangleUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyCompletionAdjunctionTriangleFields
  field_faithful := cauchyCompletionAdjunctionTriangle_field_faithful

def taste_gate : ChapterTasteGate CauchyCompletionAdjunctionTriangleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionAdjunctionTriangleChapterTasteGate

theorem CauchyCompletionAdjunctionTriangleTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyCompletionAdjunctionTriangleUp) ∧
      Nonempty (FieldFaithful CauchyCompletionAdjunctionTriangleUp) ∧
      (∀ h : BHist,
        cauchyCompletionAdjunctionTriangleDecodeBHist
            (cauchyCompletionAdjunctionTriangleEncodeBHist h) =
          h) ∧
      (∀ x : CauchyCompletionAdjunctionTriangleUp,
        cauchyCompletionAdjunctionTriangleFromEventFlow
            (cauchyCompletionAdjunctionTriangleToEventFlow x) =
          some x) ∧
      cauchyCompletionAdjunctionTriangleEncodeBHist
        (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨Nonempty.intro cauchyCompletionAdjunctionTriangleChapterTasteGate,
      Nonempty.intro cauchyCompletionAdjunctionTriangleFieldFaithful,
      cauchyCompletionAdjunctionTriangle_decode_encode_bhist,
      cauchyCompletionAdjunctionTriangle_round_trip,
      rfl⟩

end BEDC.Derived.CauchyCompletionAdjunctionTriangleUp.TasteGate
