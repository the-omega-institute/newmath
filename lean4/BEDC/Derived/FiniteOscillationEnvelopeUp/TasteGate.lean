import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteOscillationEnvelopeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteOscillationEnvelopeUp : Type where
  | mk (K X Y F B R Q U H C P N : BHist) : FiniteOscillationEnvelopeUp
  deriving DecidableEq

def finiteOscillationEnvelopeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteOscillationEnvelopeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteOscillationEnvelopeEncodeBHist h

def finiteOscillationEnvelopeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteOscillationEnvelopeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteOscillationEnvelopeDecodeBHist tail)

private theorem finiteOscillationEnvelope_decode_encode_bhist :
    ∀ h : BHist,
      finiteOscillationEnvelopeDecodeBHist (finiteOscillationEnvelopeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteOscillationEnvelopeFields : FiniteOscillationEnvelopeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteOscillationEnvelopeUp.mk K X Y F B R Q U H C P N =>
      [K, X, Y, F, B, R, Q, U, H, C, P, N]

def finiteOscillationEnvelopeToEventFlow : FiniteOscillationEnvelopeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteOscillationEnvelopeUp.mk K X Y F B R Q U H C P N =>
      [finiteOscillationEnvelopeEncodeBHist K,
        finiteOscillationEnvelopeEncodeBHist X,
        finiteOscillationEnvelopeEncodeBHist Y,
        finiteOscillationEnvelopeEncodeBHist F,
        finiteOscillationEnvelopeEncodeBHist B,
        finiteOscillationEnvelopeEncodeBHist R,
        finiteOscillationEnvelopeEncodeBHist Q,
        finiteOscillationEnvelopeEncodeBHist U,
        finiteOscillationEnvelopeEncodeBHist H,
        finiteOscillationEnvelopeEncodeBHist C,
        finiteOscillationEnvelopeEncodeBHist P,
        finiteOscillationEnvelopeEncodeBHist N]

private def finiteOscillationEnvelopeRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => finiteOscillationEnvelopeRawAt n rest

private def finiteOscillationEnvelopeLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => finiteOscillationEnvelopeLengthEq n rest

def finiteOscillationEnvelopeFromEventFlow : EventFlow → Option FiniteOscillationEnvelopeUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match finiteOscillationEnvelopeLengthEq 12 flow with
      | true =>
          some
            (FiniteOscillationEnvelopeUp.mk
              (finiteOscillationEnvelopeDecodeBHist
                (finiteOscillationEnvelopeRawAt 0 flow))
              (finiteOscillationEnvelopeDecodeBHist
                (finiteOscillationEnvelopeRawAt 1 flow))
              (finiteOscillationEnvelopeDecodeBHist
                (finiteOscillationEnvelopeRawAt 2 flow))
              (finiteOscillationEnvelopeDecodeBHist
                (finiteOscillationEnvelopeRawAt 3 flow))
              (finiteOscillationEnvelopeDecodeBHist
                (finiteOscillationEnvelopeRawAt 4 flow))
              (finiteOscillationEnvelopeDecodeBHist
                (finiteOscillationEnvelopeRawAt 5 flow))
              (finiteOscillationEnvelopeDecodeBHist
                (finiteOscillationEnvelopeRawAt 6 flow))
              (finiteOscillationEnvelopeDecodeBHist
                (finiteOscillationEnvelopeRawAt 7 flow))
              (finiteOscillationEnvelopeDecodeBHist
                (finiteOscillationEnvelopeRawAt 8 flow))
              (finiteOscillationEnvelopeDecodeBHist
                (finiteOscillationEnvelopeRawAt 9 flow))
              (finiteOscillationEnvelopeDecodeBHist
                (finiteOscillationEnvelopeRawAt 10 flow))
              (finiteOscillationEnvelopeDecodeBHist
                (finiteOscillationEnvelopeRawAt 11 flow)))
      | false => none

private theorem finiteOscillationEnvelope_round_trip :
    ∀ x : FiniteOscillationEnvelopeUp,
      finiteOscillationEnvelopeFromEventFlow (finiteOscillationEnvelopeToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K X Y F B R Q U H C P N =>
      change
        some
          (FiniteOscillationEnvelopeUp.mk
            (finiteOscillationEnvelopeDecodeBHist
              (finiteOscillationEnvelopeEncodeBHist K))
            (finiteOscillationEnvelopeDecodeBHist
              (finiteOscillationEnvelopeEncodeBHist X))
            (finiteOscillationEnvelopeDecodeBHist
              (finiteOscillationEnvelopeEncodeBHist Y))
            (finiteOscillationEnvelopeDecodeBHist
              (finiteOscillationEnvelopeEncodeBHist F))
            (finiteOscillationEnvelopeDecodeBHist
              (finiteOscillationEnvelopeEncodeBHist B))
            (finiteOscillationEnvelopeDecodeBHist
              (finiteOscillationEnvelopeEncodeBHist R))
            (finiteOscillationEnvelopeDecodeBHist
              (finiteOscillationEnvelopeEncodeBHist Q))
            (finiteOscillationEnvelopeDecodeBHist
              (finiteOscillationEnvelopeEncodeBHist U))
            (finiteOscillationEnvelopeDecodeBHist
              (finiteOscillationEnvelopeEncodeBHist H))
            (finiteOscillationEnvelopeDecodeBHist
              (finiteOscillationEnvelopeEncodeBHist C))
            (finiteOscillationEnvelopeDecodeBHist
              (finiteOscillationEnvelopeEncodeBHist P))
            (finiteOscillationEnvelopeDecodeBHist
              (finiteOscillationEnvelopeEncodeBHist N))) =
          some (FiniteOscillationEnvelopeUp.mk K X Y F B R Q U H C P N)
      rw [finiteOscillationEnvelope_decode_encode_bhist K,
        finiteOscillationEnvelope_decode_encode_bhist X,
        finiteOscillationEnvelope_decode_encode_bhist Y,
        finiteOscillationEnvelope_decode_encode_bhist F,
        finiteOscillationEnvelope_decode_encode_bhist B,
        finiteOscillationEnvelope_decode_encode_bhist R,
        finiteOscillationEnvelope_decode_encode_bhist Q,
        finiteOscillationEnvelope_decode_encode_bhist U,
        finiteOscillationEnvelope_decode_encode_bhist H,
        finiteOscillationEnvelope_decode_encode_bhist C,
        finiteOscillationEnvelope_decode_encode_bhist P,
        finiteOscillationEnvelope_decode_encode_bhist N]

private theorem finiteOscillationEnvelopeToEventFlow_injective
    {x y : FiniteOscillationEnvelopeUp} :
    finiteOscillationEnvelopeToEventFlow x = finiteOscillationEnvelopeToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteOscillationEnvelopeFromEventFlow (finiteOscillationEnvelopeToEventFlow x) =
        finiteOscillationEnvelopeFromEventFlow (finiteOscillationEnvelopeToEventFlow y) :=
    congrArg finiteOscillationEnvelopeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteOscillationEnvelope_round_trip x).symm
      (Eq.trans hread (finiteOscillationEnvelope_round_trip y)))

private theorem finiteOscillationEnvelope_field_faithful :
    ∀ x y : FiniteOscillationEnvelopeUp,
      finiteOscillationEnvelopeFields x = finiteOscillationEnvelopeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk K1 X1 Y1 F1 B1 R1 Q1 U1 H1 C1 P1 N1 =>
      cases y with
      | mk K2 X2 Y2 F2 B2 R2 Q2 U2 H2 C2 P2 N2 =>
          cases h
          rfl

instance finiteOscillationEnvelopeBHistCarrier : BHistCarrier FiniteOscillationEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteOscillationEnvelopeToEventFlow
  fromEventFlow := finiteOscillationEnvelopeFromEventFlow

instance finiteOscillationEnvelopeChapterTasteGate :
    ChapterTasteGate FiniteOscillationEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteOscillationEnvelopeFromEventFlow (finiteOscillationEnvelopeToEventFlow x) =
        some x
    exact finiteOscillationEnvelope_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteOscillationEnvelopeToEventFlow_injective heq)

instance finiteOscillationEnvelopeFieldFaithful : FieldFaithful FiniteOscillationEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteOscillationEnvelopeFields
  field_faithful := finiteOscillationEnvelope_field_faithful

instance finiteOscillationEnvelopeNontrivial : Nontrivial FiniteOscillationEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteOscillationEnvelopeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      FiniteOscillationEnvelopeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteOscillationEnvelopeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteOscillationEnvelopeChapterTasteGate

theorem FiniteOscillationEnvelopeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finiteOscillationEnvelopeDecodeBHist (finiteOscillationEnvelopeEncodeBHist h) = h) ∧
      finiteOscillationEnvelopeFields
          (FiniteOscillationEnvelopeUp.mk BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact ⟨finiteOscillationEnvelope_decode_encode_bhist, rfl⟩

end BEDC.Derived.FiniteOscillationEnvelopeUp
