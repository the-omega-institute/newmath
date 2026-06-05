import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteDimensionalSpectralGapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteDimensionalSpectralGapUp : Type where
  | mk (M T V E D R S H C P N : BHist) : FiniteDimensionalSpectralGapUp
  deriving DecidableEq

def finiteDimensionalSpectralGapEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteDimensionalSpectralGapEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteDimensionalSpectralGapEncodeBHist h

def finiteDimensionalSpectralGapDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteDimensionalSpectralGapDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteDimensionalSpectralGapDecodeBHist tail)

private theorem finiteDimensionalSpectralGapDecode_encode_bhist :
    ∀ h : BHist,
      finiteDimensionalSpectralGapDecodeBHist
          (finiteDimensionalSpectralGapEncodeBHist h) =
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

private def finiteDimensionalSpectralGapFields :
    FiniteDimensionalSpectralGapUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteDimensionalSpectralGapUp.mk M T V E D R S H C P N =>
      [M, T, V, E, D, R, S, H, C, P, N]

def finiteDimensionalSpectralGapToEventFlow : FiniteDimensionalSpectralGapUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteDimensionalSpectralGapUp.mk M T V E D R S H C P N =>
      [[BMark.b0],
        finiteDimensionalSpectralGapEncodeBHist M,
        [BMark.b1, BMark.b0],
        finiteDimensionalSpectralGapEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b0],
        finiteDimensionalSpectralGapEncodeBHist V,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteDimensionalSpectralGapEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteDimensionalSpectralGapEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteDimensionalSpectralGapEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteDimensionalSpectralGapEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        finiteDimensionalSpectralGapEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        finiteDimensionalSpectralGapEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        finiteDimensionalSpectralGapEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteDimensionalSpectralGapEncodeBHist N]

private def finiteDimensionalSpectralGapRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => finiteDimensionalSpectralGapRawAt n rest

private def finiteDimensionalSpectralGapLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => finiteDimensionalSpectralGapLengthEq n rest

def finiteDimensionalSpectralGapFromEventFlow :
    EventFlow → Option FiniteDimensionalSpectralGapUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match finiteDimensionalSpectralGapLengthEq 22 flow with
      | true =>
          some
            (FiniteDimensionalSpectralGapUp.mk
              (finiteDimensionalSpectralGapDecodeBHist
                (finiteDimensionalSpectralGapRawAt 1 flow))
              (finiteDimensionalSpectralGapDecodeBHist
                (finiteDimensionalSpectralGapRawAt 3 flow))
              (finiteDimensionalSpectralGapDecodeBHist
                (finiteDimensionalSpectralGapRawAt 5 flow))
              (finiteDimensionalSpectralGapDecodeBHist
                (finiteDimensionalSpectralGapRawAt 7 flow))
              (finiteDimensionalSpectralGapDecodeBHist
                (finiteDimensionalSpectralGapRawAt 9 flow))
              (finiteDimensionalSpectralGapDecodeBHist
                (finiteDimensionalSpectralGapRawAt 11 flow))
              (finiteDimensionalSpectralGapDecodeBHist
                (finiteDimensionalSpectralGapRawAt 13 flow))
              (finiteDimensionalSpectralGapDecodeBHist
                (finiteDimensionalSpectralGapRawAt 15 flow))
              (finiteDimensionalSpectralGapDecodeBHist
                (finiteDimensionalSpectralGapRawAt 17 flow))
              (finiteDimensionalSpectralGapDecodeBHist
                (finiteDimensionalSpectralGapRawAt 19 flow))
              (finiteDimensionalSpectralGapDecodeBHist
                (finiteDimensionalSpectralGapRawAt 21 flow)))
      | false => none

private theorem finiteDimensionalSpectralGap_round_trip :
    ∀ x : FiniteDimensionalSpectralGapUp,
      finiteDimensionalSpectralGapFromEventFlow
          (finiteDimensionalSpectralGapToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M T V E D R S H C P N =>
      change
        some
          (FiniteDimensionalSpectralGapUp.mk
            (finiteDimensionalSpectralGapDecodeBHist
              (finiteDimensionalSpectralGapEncodeBHist M))
            (finiteDimensionalSpectralGapDecodeBHist
              (finiteDimensionalSpectralGapEncodeBHist T))
            (finiteDimensionalSpectralGapDecodeBHist
              (finiteDimensionalSpectralGapEncodeBHist V))
            (finiteDimensionalSpectralGapDecodeBHist
              (finiteDimensionalSpectralGapEncodeBHist E))
            (finiteDimensionalSpectralGapDecodeBHist
              (finiteDimensionalSpectralGapEncodeBHist D))
            (finiteDimensionalSpectralGapDecodeBHist
              (finiteDimensionalSpectralGapEncodeBHist R))
            (finiteDimensionalSpectralGapDecodeBHist
              (finiteDimensionalSpectralGapEncodeBHist S))
            (finiteDimensionalSpectralGapDecodeBHist
              (finiteDimensionalSpectralGapEncodeBHist H))
            (finiteDimensionalSpectralGapDecodeBHist
              (finiteDimensionalSpectralGapEncodeBHist C))
            (finiteDimensionalSpectralGapDecodeBHist
              (finiteDimensionalSpectralGapEncodeBHist P))
            (finiteDimensionalSpectralGapDecodeBHist
              (finiteDimensionalSpectralGapEncodeBHist N))) =
          some (FiniteDimensionalSpectralGapUp.mk M T V E D R S H C P N)
      rw [finiteDimensionalSpectralGapDecode_encode_bhist M,
        finiteDimensionalSpectralGapDecode_encode_bhist T,
        finiteDimensionalSpectralGapDecode_encode_bhist V,
        finiteDimensionalSpectralGapDecode_encode_bhist E,
        finiteDimensionalSpectralGapDecode_encode_bhist D,
        finiteDimensionalSpectralGapDecode_encode_bhist R,
        finiteDimensionalSpectralGapDecode_encode_bhist S,
        finiteDimensionalSpectralGapDecode_encode_bhist H,
        finiteDimensionalSpectralGapDecode_encode_bhist C,
        finiteDimensionalSpectralGapDecode_encode_bhist P,
        finiteDimensionalSpectralGapDecode_encode_bhist N]

private theorem finiteDimensionalSpectralGapToEventFlow_injective
    {x y : FiniteDimensionalSpectralGapUp} :
    finiteDimensionalSpectralGapToEventFlow x =
        finiteDimensionalSpectralGapToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteDimensionalSpectralGapFromEventFlow
          (finiteDimensionalSpectralGapToEventFlow x) =
        finiteDimensionalSpectralGapFromEventFlow
          (finiteDimensionalSpectralGapToEventFlow y) :=
    congrArg finiteDimensionalSpectralGapFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteDimensionalSpectralGap_round_trip x).symm
      (Eq.trans hread (finiteDimensionalSpectralGap_round_trip y)))

private theorem finiteDimensionalSpectralGap_field_faithful :
    ∀ x y : FiniteDimensionalSpectralGapUp,
      finiteDimensionalSpectralGapFields x =
          finiteDimensionalSpectralGapFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 T1 V1 E1 D1 R1 S1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 T2 V2 E2 D2 R2 S2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance finiteDimensionalSpectralGapBHistCarrier :
    BHistCarrier FiniteDimensionalSpectralGapUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteDimensionalSpectralGapToEventFlow
  fromEventFlow := finiteDimensionalSpectralGapFromEventFlow

instance finiteDimensionalSpectralGapChapterTasteGate :
    ChapterTasteGate FiniteDimensionalSpectralGapUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteDimensionalSpectralGapFromEventFlow
          (finiteDimensionalSpectralGapToEventFlow x) =
        some x
    exact finiteDimensionalSpectralGap_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteDimensionalSpectralGapToEventFlow_injective heq)

instance finiteDimensionalSpectralGapFieldFaithful :
    FieldFaithful FiniteDimensionalSpectralGapUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteDimensionalSpectralGapFields
  field_faithful := finiteDimensionalSpectralGap_field_faithful

instance finiteDimensionalSpectralGapNontrivial :
    Nontrivial FiniteDimensionalSpectralGapUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteDimensionalSpectralGapUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      FiniteDimensionalSpectralGapUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem FiniteDimensionalSpectralGapTasteGate_single_carrier_alignment :
    finiteDimensionalSpectralGapEncodeBHist BHist.Empty = ([] : RawEvent) ∧
      finiteDimensionalSpectralGapEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
      (∀ h : BHist,
        finiteDimensionalSpectralGapDecodeBHist
            (finiteDimensionalSpectralGapEncodeBHist h) =
          h) ∧
      (∀ x : FiniteDimensionalSpectralGapUp,
        finiteDimensionalSpectralGapFromEventFlow
            (finiteDimensionalSpectralGapToEventFlow x) =
          some x) ∧
      (∀ x y : FiniteDimensionalSpectralGapUp,
        finiteDimensionalSpectralGapToEventFlow x =
            finiteDimensionalSpectralGapToEventFlow y →
          x = y) ∧
      Nonempty (FieldFaithful FiniteDimensionalSpectralGapUp) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨rfl, rfl, finiteDimensionalSpectralGapDecode_encode_bhist,
      finiteDimensionalSpectralGap_round_trip,
      (fun _ _ heq => finiteDimensionalSpectralGapToEventFlow_injective heq),
      ⟨finiteDimensionalSpectralGapFieldFaithful⟩⟩

end BEDC.Derived.FiniteDimensionalSpectralGapUp
