import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.IntervalCauchyCompletenessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive IntervalCauchyCompletenessUp : Type where
  | mk (B Q D W R E H C P N : BHist) : IntervalCauchyCompletenessUp
  deriving DecidableEq

def intervalCauchyCompletenessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: intervalCauchyCompletenessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: intervalCauchyCompletenessEncodeBHist h

def intervalCauchyCompletenessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (intervalCauchyCompletenessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (intervalCauchyCompletenessDecodeBHist tail)

private theorem intervalCauchyCompletenessDecodeEncode :
    ∀ h : BHist,
      intervalCauchyCompletenessDecodeBHist (intervalCauchyCompletenessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def intervalCauchyCompletenessToEventFlow : IntervalCauchyCompletenessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | IntervalCauchyCompletenessUp.mk B Q D W R E H C P N =>
      [[BMark.b0],
        intervalCauchyCompletenessEncodeBHist B,
        [BMark.b1, BMark.b0],
        intervalCauchyCompletenessEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b0],
        intervalCauchyCompletenessEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        intervalCauchyCompletenessEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        intervalCauchyCompletenessEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        intervalCauchyCompletenessEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        intervalCauchyCompletenessEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        intervalCauchyCompletenessEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        intervalCauchyCompletenessEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        intervalCauchyCompletenessEncodeBHist N]

private def intervalCauchyCompletenessEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => intervalCauchyCompletenessEventAtDefault index rest

def intervalCauchyCompletenessFromEventFlow
    (ef : EventFlow) : Option IntervalCauchyCompletenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (IntervalCauchyCompletenessUp.mk
      (intervalCauchyCompletenessDecodeBHist (intervalCauchyCompletenessEventAtDefault 1 ef))
      (intervalCauchyCompletenessDecodeBHist (intervalCauchyCompletenessEventAtDefault 3 ef))
      (intervalCauchyCompletenessDecodeBHist (intervalCauchyCompletenessEventAtDefault 5 ef))
      (intervalCauchyCompletenessDecodeBHist (intervalCauchyCompletenessEventAtDefault 7 ef))
      (intervalCauchyCompletenessDecodeBHist (intervalCauchyCompletenessEventAtDefault 9 ef))
      (intervalCauchyCompletenessDecodeBHist (intervalCauchyCompletenessEventAtDefault 11 ef))
      (intervalCauchyCompletenessDecodeBHist (intervalCauchyCompletenessEventAtDefault 13 ef))
      (intervalCauchyCompletenessDecodeBHist (intervalCauchyCompletenessEventAtDefault 15 ef))
      (intervalCauchyCompletenessDecodeBHist (intervalCauchyCompletenessEventAtDefault 17 ef))
      (intervalCauchyCompletenessDecodeBHist (intervalCauchyCompletenessEventAtDefault 19 ef)))

private theorem intervalCauchyCompletenessRoundTrip :
    ∀ x : IntervalCauchyCompletenessUp,
      intervalCauchyCompletenessFromEventFlow
        (intervalCauchyCompletenessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B Q D W R E H C P N =>
      change
        some
          (IntervalCauchyCompletenessUp.mk
            (intervalCauchyCompletenessDecodeBHist (intervalCauchyCompletenessEncodeBHist B))
            (intervalCauchyCompletenessDecodeBHist (intervalCauchyCompletenessEncodeBHist Q))
            (intervalCauchyCompletenessDecodeBHist (intervalCauchyCompletenessEncodeBHist D))
            (intervalCauchyCompletenessDecodeBHist (intervalCauchyCompletenessEncodeBHist W))
            (intervalCauchyCompletenessDecodeBHist (intervalCauchyCompletenessEncodeBHist R))
            (intervalCauchyCompletenessDecodeBHist (intervalCauchyCompletenessEncodeBHist E))
            (intervalCauchyCompletenessDecodeBHist (intervalCauchyCompletenessEncodeBHist H))
            (intervalCauchyCompletenessDecodeBHist (intervalCauchyCompletenessEncodeBHist C))
            (intervalCauchyCompletenessDecodeBHist (intervalCauchyCompletenessEncodeBHist P))
            (intervalCauchyCompletenessDecodeBHist (intervalCauchyCompletenessEncodeBHist N))) =
          some (IntervalCauchyCompletenessUp.mk B Q D W R E H C P N)
      rw [intervalCauchyCompletenessDecodeEncode B,
        intervalCauchyCompletenessDecodeEncode Q, intervalCauchyCompletenessDecodeEncode D,
        intervalCauchyCompletenessDecodeEncode W, intervalCauchyCompletenessDecodeEncode R,
        intervalCauchyCompletenessDecodeEncode E, intervalCauchyCompletenessDecodeEncode H,
        intervalCauchyCompletenessDecodeEncode C, intervalCauchyCompletenessDecodeEncode P,
        intervalCauchyCompletenessDecodeEncode N]

private theorem intervalCauchyCompletenessToEventFlow_injective
    {x y : IntervalCauchyCompletenessUp} :
    intervalCauchyCompletenessToEventFlow x =
      intervalCauchyCompletenessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      intervalCauchyCompletenessFromEventFlow (intervalCauchyCompletenessToEventFlow x) =
        intervalCauchyCompletenessFromEventFlow (intervalCauchyCompletenessToEventFlow y) :=
    congrArg intervalCauchyCompletenessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (intervalCauchyCompletenessRoundTrip x).symm
      (Eq.trans hread (intervalCauchyCompletenessRoundTrip y)))

def intervalCauchyCompletenessFields : IntervalCauchyCompletenessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | IntervalCauchyCompletenessUp.mk B Q D W R E H C P N => [B, Q, D, W, R, E, H, C, P, N]

instance intervalCauchyCompletenessBHistCarrier :
    BHistCarrier IntervalCauchyCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := intervalCauchyCompletenessToEventFlow
  fromEventFlow := intervalCauchyCompletenessFromEventFlow

instance intervalCauchyCompletenessChapterTasteGate :
    ChapterTasteGate IntervalCauchyCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      intervalCauchyCompletenessFromEventFlow
        (intervalCauchyCompletenessToEventFlow x) = some x
    exact intervalCauchyCompletenessRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (intervalCauchyCompletenessToEventFlow_injective heq)

instance intervalCauchyCompletenessFieldFaithful :
    FieldFaithful IntervalCauchyCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := intervalCauchyCompletenessFields
  field_faithful := by
    intro x y h
    cases x with
    | mk B₁ Q₁ D₁ W₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk B₂ Q₂ D₂ W₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
        change [B₁, Q₁, D₁, W₁, R₁, E₁, H₁, C₁, P₁, N₁] =
          [B₂, Q₂, D₂, W₂, R₂, E₂, H₂, C₂, P₂, N₂] at h
        cases h
        rfl

instance intervalCauchyCompletenessNontrivial :
    Nontrivial IntervalCauchyCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨IntervalCauchyCompletenessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      IntervalCauchyCompletenessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem IntervalCauchyCompletenessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      intervalCauchyCompletenessDecodeBHist (intervalCauchyCompletenessEncodeBHist h) = h) ∧
      (∀ x : IntervalCauchyCompletenessUp,
        intervalCauchyCompletenessFromEventFlow (intervalCauchyCompletenessToEventFlow x) =
          some x) ∧
        (∀ x y : IntervalCauchyCompletenessUp,
          intervalCauchyCompletenessToEventFlow x =
            intervalCauchyCompletenessToEventFlow y → x = y) ∧
          intervalCauchyCompletenessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨intervalCauchyCompletenessDecodeEncode,
      intervalCauchyCompletenessRoundTrip,
      fun _ _ heq => intervalCauchyCompletenessToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.IntervalCauchyCompletenessUp
