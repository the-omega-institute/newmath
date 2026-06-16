import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.WobbleSaturationSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive WobbleSaturationSealUp : Type where
  | mk (W T C Q R D A H K P N : BHist) : WobbleSaturationSealUp
  deriving DecidableEq

def wobbleSaturationSealEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: wobbleSaturationSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: wobbleSaturationSealEncodeBHist h

def wobbleSaturationSealDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (wobbleSaturationSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (wobbleSaturationSealDecodeBHist tail)

private theorem WobbleSaturationSealTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      wobbleSaturationSealDecodeBHist
          (wobbleSaturationSealEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def wobbleSaturationSealFields : WobbleSaturationSealUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | WobbleSaturationSealUp.mk W T C Q R D A H K P N =>
      [W, T, C, Q, R, D, A, H, K, P, N]

def wobbleSaturationSealToEventFlow : WobbleSaturationSealUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (wobbleSaturationSealFields x).map wobbleSaturationSealEncodeBHist

private def wobbleSaturationSealEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      wobbleSaturationSealEventAtDefault index rest

def wobbleSaturationSealFromEventFlow :
    EventFlow -> Option WobbleSaturationSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (WobbleSaturationSealUp.mk
        (wobbleSaturationSealDecodeBHist (wobbleSaturationSealEventAtDefault 0 ef))
        (wobbleSaturationSealDecodeBHist (wobbleSaturationSealEventAtDefault 1 ef))
        (wobbleSaturationSealDecodeBHist (wobbleSaturationSealEventAtDefault 2 ef))
        (wobbleSaturationSealDecodeBHist (wobbleSaturationSealEventAtDefault 3 ef))
        (wobbleSaturationSealDecodeBHist (wobbleSaturationSealEventAtDefault 4 ef))
        (wobbleSaturationSealDecodeBHist (wobbleSaturationSealEventAtDefault 5 ef))
        (wobbleSaturationSealDecodeBHist (wobbleSaturationSealEventAtDefault 6 ef))
        (wobbleSaturationSealDecodeBHist (wobbleSaturationSealEventAtDefault 7 ef))
        (wobbleSaturationSealDecodeBHist (wobbleSaturationSealEventAtDefault 8 ef))
        (wobbleSaturationSealDecodeBHist (wobbleSaturationSealEventAtDefault 9 ef))
        (wobbleSaturationSealDecodeBHist (wobbleSaturationSealEventAtDefault 10 ef)))

private theorem WobbleSaturationSealTasteGate_single_carrier_alignment_round_trip
    (x : WobbleSaturationSealUp) :
    wobbleSaturationSealFromEventFlow (wobbleSaturationSealToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk W T C Q R D A H K P N =>
      change
        some
          (WobbleSaturationSealUp.mk
            (wobbleSaturationSealDecodeBHist (wobbleSaturationSealEncodeBHist W))
            (wobbleSaturationSealDecodeBHist (wobbleSaturationSealEncodeBHist T))
            (wobbleSaturationSealDecodeBHist (wobbleSaturationSealEncodeBHist C))
            (wobbleSaturationSealDecodeBHist (wobbleSaturationSealEncodeBHist Q))
            (wobbleSaturationSealDecodeBHist (wobbleSaturationSealEncodeBHist R))
            (wobbleSaturationSealDecodeBHist (wobbleSaturationSealEncodeBHist D))
            (wobbleSaturationSealDecodeBHist (wobbleSaturationSealEncodeBHist A))
            (wobbleSaturationSealDecodeBHist (wobbleSaturationSealEncodeBHist H))
            (wobbleSaturationSealDecodeBHist (wobbleSaturationSealEncodeBHist K))
            (wobbleSaturationSealDecodeBHist (wobbleSaturationSealEncodeBHist P))
            (wobbleSaturationSealDecodeBHist (wobbleSaturationSealEncodeBHist N))) =
          some (WobbleSaturationSealUp.mk W T C Q R D A H K P N)
      rw [WobbleSaturationSealTasteGate_single_carrier_alignment_decode_encode W,
        WobbleSaturationSealTasteGate_single_carrier_alignment_decode_encode T,
        WobbleSaturationSealTasteGate_single_carrier_alignment_decode_encode C,
        WobbleSaturationSealTasteGate_single_carrier_alignment_decode_encode Q,
        WobbleSaturationSealTasteGate_single_carrier_alignment_decode_encode R,
        WobbleSaturationSealTasteGate_single_carrier_alignment_decode_encode D,
        WobbleSaturationSealTasteGate_single_carrier_alignment_decode_encode A,
        WobbleSaturationSealTasteGate_single_carrier_alignment_decode_encode H,
        WobbleSaturationSealTasteGate_single_carrier_alignment_decode_encode K,
        WobbleSaturationSealTasteGate_single_carrier_alignment_decode_encode P,
        WobbleSaturationSealTasteGate_single_carrier_alignment_decode_encode N]

private theorem WobbleSaturationSealTasteGate_single_carrier_alignment_injective
    {x y : WobbleSaturationSealUp} :
    wobbleSaturationSealToEventFlow x =
        wobbleSaturationSealToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      wobbleSaturationSealFromEventFlow (wobbleSaturationSealToEventFlow x) =
        wobbleSaturationSealFromEventFlow (wobbleSaturationSealToEventFlow y) :=
    congrArg wobbleSaturationSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (WobbleSaturationSealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (WobbleSaturationSealTasteGate_single_carrier_alignment_round_trip y)))

private theorem WobbleSaturationSealTasteGate_single_carrier_alignment_fields :
    forall x y : WobbleSaturationSealUp,
      wobbleSaturationSealFields x =
        wobbleSaturationSealFields y ->
          x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk W1 T1 C1 Q1 R1 D1 A1 H1 K1 P1 N1 =>
      cases y with
      | mk W2 T2 C2 Q2 R2 D2 A2 H2 K2 P2 N2 =>
          cases hfields
          rfl

instance wobbleSaturationSealBHistCarrier :
    BHistCarrier WobbleSaturationSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := wobbleSaturationSealToEventFlow
  fromEventFlow := wobbleSaturationSealFromEventFlow

instance wobbleSaturationSealChapterTasteGate :
    ChapterTasteGate WobbleSaturationSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      wobbleSaturationSealFromEventFlow (wobbleSaturationSealToEventFlow x) =
        some x
    exact WobbleSaturationSealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (WobbleSaturationSealTasteGate_single_carrier_alignment_injective heq)

instance wobbleSaturationSealFieldFaithful :
    FieldFaithful WobbleSaturationSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := wobbleSaturationSealFields
  field_faithful := WobbleSaturationSealTasteGate_single_carrier_alignment_fields

instance wobbleSaturationSealNontrivial :
    Nontrivial WobbleSaturationSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨WobbleSaturationSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      WobbleSaturationSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate WobbleSaturationSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  wobbleSaturationSealChapterTasteGate

theorem WobbleSaturationSealTasteGate_single_carrier_alignment :
    (forall h : BHist,
      wobbleSaturationSealDecodeBHist
          (wobbleSaturationSealEncodeBHist h) =
        h) ∧
      (forall x : WobbleSaturationSealUp,
        wobbleSaturationSealFromEventFlow (wobbleSaturationSealToEventFlow x) =
          some x) ∧
        (forall x y : WobbleSaturationSealUp,
          wobbleSaturationSealToEventFlow x =
              wobbleSaturationSealToEventFlow y ->
            x = y) ∧
          (forall x y : WobbleSaturationSealUp,
            wobbleSaturationSealFields x =
                wobbleSaturationSealFields y ->
              x = y) ∧
            (exists x y : WobbleSaturationSealUp, x ≠ y) ∧
              wobbleSaturationSealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact WobbleSaturationSealTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact WobbleSaturationSealTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact WobbleSaturationSealTasteGate_single_carrier_alignment_injective heq
      · constructor
        · exact WobbleSaturationSealTasteGate_single_carrier_alignment_fields
        · constructor
          · exact
              ⟨WobbleSaturationSealUp.mk BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty,
                WobbleSaturationSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                by
                  intro h
                  cases h⟩
          · rfl

end BEDC.Derived.WobbleSaturationSealUp
