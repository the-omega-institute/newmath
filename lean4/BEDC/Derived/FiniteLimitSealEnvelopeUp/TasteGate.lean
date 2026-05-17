import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteLimitSealEnvelopeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteLimitSealEnvelopeUp : Type where
  | mk (W R D L Q H C P N : BHist) : FiniteLimitSealEnvelopeUp
  deriving DecidableEq

def finiteLimitSealEnvelopeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteLimitSealEnvelopeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteLimitSealEnvelopeEncodeBHist h

def finiteLimitSealEnvelopeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteLimitSealEnvelopeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteLimitSealEnvelopeDecodeBHist tail)

private theorem finiteLimitSealEnvelopeDecode_encode_bhist :
    ∀ h : BHist,
      finiteLimitSealEnvelopeDecodeBHist (finiteLimitSealEnvelopeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteLimitSealEnvelopeToEventFlow : FiniteLimitSealEnvelopeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteLimitSealEnvelopeUp.mk W R D L Q H C P N =>
      [[BMark.b0, BMark.b0],
        finiteLimitSealEnvelopeEncodeBHist W,
        [BMark.b0, BMark.b1],
        finiteLimitSealEnvelopeEncodeBHist R,
        [BMark.b1, BMark.b0, BMark.b0],
        finiteLimitSealEnvelopeEncodeBHist D,
        [BMark.b1, BMark.b0, BMark.b1],
        finiteLimitSealEnvelopeEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b0],
        finiteLimitSealEnvelopeEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteLimitSealEnvelopeEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteLimitSealEnvelopeEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteLimitSealEnvelopeEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteLimitSealEnvelopeEncodeBHist N]

private def finiteLimitSealEnvelopeRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => finiteLimitSealEnvelopeRawAt n rest

private def finiteLimitSealEnvelopeLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => finiteLimitSealEnvelopeLengthEq n rest

def finiteLimitSealEnvelopeFromEventFlow : EventFlow → Option FiniteLimitSealEnvelopeUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match finiteLimitSealEnvelopeLengthEq 18 flow with
      | true =>
          some
            (FiniteLimitSealEnvelopeUp.mk
              (finiteLimitSealEnvelopeDecodeBHist (finiteLimitSealEnvelopeRawAt 1 flow))
              (finiteLimitSealEnvelopeDecodeBHist (finiteLimitSealEnvelopeRawAt 3 flow))
              (finiteLimitSealEnvelopeDecodeBHist (finiteLimitSealEnvelopeRawAt 5 flow))
              (finiteLimitSealEnvelopeDecodeBHist (finiteLimitSealEnvelopeRawAt 7 flow))
              (finiteLimitSealEnvelopeDecodeBHist (finiteLimitSealEnvelopeRawAt 9 flow))
              (finiteLimitSealEnvelopeDecodeBHist (finiteLimitSealEnvelopeRawAt 11 flow))
              (finiteLimitSealEnvelopeDecodeBHist (finiteLimitSealEnvelopeRawAt 13 flow))
              (finiteLimitSealEnvelopeDecodeBHist (finiteLimitSealEnvelopeRawAt 15 flow))
              (finiteLimitSealEnvelopeDecodeBHist (finiteLimitSealEnvelopeRawAt 17 flow)))
      | false => none

def finiteLimitSealEnvelopeFields : FiniteLimitSealEnvelopeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteLimitSealEnvelopeUp.mk W R D L Q H C P N => [W, R, D, L, Q, H, C, P, N]

private theorem finiteLimitSealEnvelope_round_trip :
    ∀ x : FiniteLimitSealEnvelopeUp,
      finiteLimitSealEnvelopeFromEventFlow
          (finiteLimitSealEnvelopeToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W R D L Q H C P N =>
      change
        some
          (FiniteLimitSealEnvelopeUp.mk
            (finiteLimitSealEnvelopeDecodeBHist (finiteLimitSealEnvelopeEncodeBHist W))
            (finiteLimitSealEnvelopeDecodeBHist (finiteLimitSealEnvelopeEncodeBHist R))
            (finiteLimitSealEnvelopeDecodeBHist (finiteLimitSealEnvelopeEncodeBHist D))
            (finiteLimitSealEnvelopeDecodeBHist (finiteLimitSealEnvelopeEncodeBHist L))
            (finiteLimitSealEnvelopeDecodeBHist (finiteLimitSealEnvelopeEncodeBHist Q))
            (finiteLimitSealEnvelopeDecodeBHist (finiteLimitSealEnvelopeEncodeBHist H))
            (finiteLimitSealEnvelopeDecodeBHist (finiteLimitSealEnvelopeEncodeBHist C))
            (finiteLimitSealEnvelopeDecodeBHist (finiteLimitSealEnvelopeEncodeBHist P))
            (finiteLimitSealEnvelopeDecodeBHist (finiteLimitSealEnvelopeEncodeBHist N))) =
          some (FiniteLimitSealEnvelopeUp.mk W R D L Q H C P N)
      rw [finiteLimitSealEnvelopeDecode_encode_bhist W,
        finiteLimitSealEnvelopeDecode_encode_bhist R,
        finiteLimitSealEnvelopeDecode_encode_bhist D,
        finiteLimitSealEnvelopeDecode_encode_bhist L,
        finiteLimitSealEnvelopeDecode_encode_bhist Q,
        finiteLimitSealEnvelopeDecode_encode_bhist H,
        finiteLimitSealEnvelopeDecode_encode_bhist C,
        finiteLimitSealEnvelopeDecode_encode_bhist P,
        finiteLimitSealEnvelopeDecode_encode_bhist N]

private theorem finiteLimitSealEnvelopeToEventFlow_injective
    {x y : FiniteLimitSealEnvelopeUp} :
    finiteLimitSealEnvelopeToEventFlow x =
        finiteLimitSealEnvelopeToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          finiteLimitSealEnvelopeFromEventFlow
            (finiteLimitSealEnvelopeToEventFlow x) :=
        (finiteLimitSealEnvelope_round_trip x).symm
      _ =
          finiteLimitSealEnvelopeFromEventFlow
            (finiteLimitSealEnvelopeToEventFlow y) :=
        congrArg finiteLimitSealEnvelopeFromEventFlow hxy
      _ = some y := finiteLimitSealEnvelope_round_trip y
  exact Option.some.inj optionEq

private theorem finiteLimitSealEnvelope_field_faithful :
    ∀ x y : FiniteLimitSealEnvelopeUp,
      finiteLimitSealEnvelopeFields x = finiteLimitSealEnvelopeFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk W1 R1 D1 L1 Q1 H1 C1 P1 N1 =>
      cases y with
      | mk W2 R2 D2 L2 Q2 H2 C2 P2 N2 =>
          injection h with hW t1
          injection t1 with hR t2
          injection t2 with hD t3
          injection t3 with hL t4
          injection t4 with hQ t5
          injection t5 with hH t6
          injection t6 with hC t7
          injection t7 with hP t8
          injection t8 with hN _
          cases hW
          cases hR
          cases hD
          cases hL
          cases hQ
          cases hH
          cases hC
          cases hP
          cases hN
          rfl

instance finiteLimitSealEnvelopeBHistCarrier : BHistCarrier FiniteLimitSealEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteLimitSealEnvelopeToEventFlow
  fromEventFlow := finiteLimitSealEnvelopeFromEventFlow

instance finiteLimitSealEnvelopeChapterTasteGate :
    ChapterTasteGate FiniteLimitSealEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteLimitSealEnvelopeFromEventFlow
          (finiteLimitSealEnvelopeToEventFlow x) =
        some x
    exact finiteLimitSealEnvelope_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteLimitSealEnvelopeToEventFlow_injective heq)

instance finiteLimitSealEnvelopeFieldFaithful :
    FieldFaithful FiniteLimitSealEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteLimitSealEnvelopeFields
  field_faithful := finiteLimitSealEnvelope_field_faithful

instance finiteLimitSealEnvelopeNontrivial : Nontrivial FiniteLimitSealEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteLimitSealEnvelopeUp.mk
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      FiniteLimitSealEnvelopeUp.mk
        (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteLimitSealEnvelopeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteLimitSealEnvelopeChapterTasteGate

theorem FiniteLimitSealEnvelopeTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteLimitSealEnvelopeDecodeBHist (finiteLimitSealEnvelopeEncodeBHist h) = h) ∧
      (∀ x : FiniteLimitSealEnvelopeUp,
        finiteLimitSealEnvelopeFromEventFlow (finiteLimitSealEnvelopeToEventFlow x) = some x) ∧
        (∀ x y : FiniteLimitSealEnvelopeUp,
          finiteLimitSealEnvelopeToEventFlow x = finiteLimitSealEnvelopeToEventFlow y → x = y) ∧
          finiteLimitSealEnvelopeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact finiteLimitSealEnvelopeDecode_encode_bhist
  · constructor
    · exact finiteLimitSealEnvelope_round_trip
    · constructor
      · intro x y heq
        have optionEq : some x = some y := by
          calc
            some x =
                finiteLimitSealEnvelopeFromEventFlow
                  (finiteLimitSealEnvelopeToEventFlow x) :=
              (finiteLimitSealEnvelope_round_trip x).symm
            _ =
                finiteLimitSealEnvelopeFromEventFlow
                  (finiteLimitSealEnvelopeToEventFlow y) :=
              congrArg finiteLimitSealEnvelopeFromEventFlow heq
            _ = some y := finiteLimitSealEnvelope_round_trip y
        exact Option.some.inj optionEq
      · rfl

end BEDC.Derived.FiniteLimitSealEnvelopeUp
