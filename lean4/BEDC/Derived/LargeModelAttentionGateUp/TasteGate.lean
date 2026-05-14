import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LargeModelAttentionGateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LargeModelAttentionGateUp : Type where
  | mk : (T A C K U V H R P N : BHist) → LargeModelAttentionGateUp
  deriving DecidableEq

def largeModelAttentionGateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: largeModelAttentionGateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: largeModelAttentionGateEncodeBHist h

def largeModelAttentionGateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (largeModelAttentionGateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (largeModelAttentionGateDecodeBHist tail)

private theorem largeModelAttentionGateDecode_encode_bhist :
    ∀ h : BHist,
      largeModelAttentionGateDecodeBHist (largeModelAttentionGateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def largeModelAttentionGateToEventFlow : LargeModelAttentionGateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LargeModelAttentionGateUp.mk T A C K U V H R P N =>
      [[BMark.b0],
        largeModelAttentionGateEncodeBHist T,
        [BMark.b1, BMark.b0],
        largeModelAttentionGateEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b0],
        largeModelAttentionGateEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        largeModelAttentionGateEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        largeModelAttentionGateEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        largeModelAttentionGateEncodeBHist V,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        largeModelAttentionGateEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        largeModelAttentionGateEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        largeModelAttentionGateEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        largeModelAttentionGateEncodeBHist N]

private def largeModelAttentionGateEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => largeModelAttentionGateEventAtDefault index rest

def largeModelAttentionGateFromEventFlow (ef : EventFlow) :
    Option LargeModelAttentionGateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LargeModelAttentionGateUp.mk
      (largeModelAttentionGateDecodeBHist (largeModelAttentionGateEventAtDefault 1 ef))
      (largeModelAttentionGateDecodeBHist (largeModelAttentionGateEventAtDefault 3 ef))
      (largeModelAttentionGateDecodeBHist (largeModelAttentionGateEventAtDefault 5 ef))
      (largeModelAttentionGateDecodeBHist (largeModelAttentionGateEventAtDefault 7 ef))
      (largeModelAttentionGateDecodeBHist (largeModelAttentionGateEventAtDefault 9 ef))
      (largeModelAttentionGateDecodeBHist (largeModelAttentionGateEventAtDefault 11 ef))
      (largeModelAttentionGateDecodeBHist (largeModelAttentionGateEventAtDefault 13 ef))
      (largeModelAttentionGateDecodeBHist (largeModelAttentionGateEventAtDefault 15 ef))
      (largeModelAttentionGateDecodeBHist (largeModelAttentionGateEventAtDefault 17 ef))
      (largeModelAttentionGateDecodeBHist (largeModelAttentionGateEventAtDefault 19 ef)))

private theorem largeModelAttentionGate_round_trip :
    ∀ x : LargeModelAttentionGateUp,
      largeModelAttentionGateFromEventFlow (largeModelAttentionGateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T A C K U V H R P N =>
      change
        some
          (LargeModelAttentionGateUp.mk
            (largeModelAttentionGateDecodeBHist (largeModelAttentionGateEncodeBHist T))
            (largeModelAttentionGateDecodeBHist (largeModelAttentionGateEncodeBHist A))
            (largeModelAttentionGateDecodeBHist (largeModelAttentionGateEncodeBHist C))
            (largeModelAttentionGateDecodeBHist (largeModelAttentionGateEncodeBHist K))
            (largeModelAttentionGateDecodeBHist (largeModelAttentionGateEncodeBHist U))
            (largeModelAttentionGateDecodeBHist (largeModelAttentionGateEncodeBHist V))
            (largeModelAttentionGateDecodeBHist (largeModelAttentionGateEncodeBHist H))
            (largeModelAttentionGateDecodeBHist (largeModelAttentionGateEncodeBHist R))
            (largeModelAttentionGateDecodeBHist (largeModelAttentionGateEncodeBHist P))
            (largeModelAttentionGateDecodeBHist (largeModelAttentionGateEncodeBHist N))) =
          some (LargeModelAttentionGateUp.mk T A C K U V H R P N)
      rw [largeModelAttentionGateDecode_encode_bhist T,
        largeModelAttentionGateDecode_encode_bhist A,
        largeModelAttentionGateDecode_encode_bhist C,
        largeModelAttentionGateDecode_encode_bhist K,
        largeModelAttentionGateDecode_encode_bhist U,
        largeModelAttentionGateDecode_encode_bhist V,
        largeModelAttentionGateDecode_encode_bhist H,
        largeModelAttentionGateDecode_encode_bhist R,
        largeModelAttentionGateDecode_encode_bhist P,
        largeModelAttentionGateDecode_encode_bhist N]

private theorem largeModelAttentionGateToEventFlow_injective
    {x y : LargeModelAttentionGateUp} :
    largeModelAttentionGateToEventFlow x = largeModelAttentionGateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      largeModelAttentionGateFromEventFlow (largeModelAttentionGateToEventFlow x) =
        largeModelAttentionGateFromEventFlow (largeModelAttentionGateToEventFlow y) :=
    congrArg largeModelAttentionGateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (largeModelAttentionGate_round_trip x).symm
      (Eq.trans hread (largeModelAttentionGate_round_trip y)))

instance largeModelAttentionGateBHistCarrier : BHistCarrier LargeModelAttentionGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := largeModelAttentionGateToEventFlow
  fromEventFlow := largeModelAttentionGateFromEventFlow

instance largeModelAttentionGateChapterTasteGate :
    ChapterTasteGate LargeModelAttentionGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change largeModelAttentionGateFromEventFlow (largeModelAttentionGateToEventFlow x) = some x
    exact largeModelAttentionGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (largeModelAttentionGateToEventFlow_injective heq)

instance largeModelAttentionGateFieldFaithful : FieldFaithful LargeModelAttentionGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | LargeModelAttentionGateUp.mk T A C K U V H R P N => [T, A, C, K, U, V, H, R, P, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk T1 A1 C1 K1 U1 V1 H1 R1 P1 N1 =>
        cases y with
        | mk T2 A2 C2 K2 U2 V2 H2 R2 P2 N2 =>
            injection h with hT t1
            injection t1 with hA t2
            injection t2 with hC t3
            injection t3 with hK t4
            injection t4 with hU t5
            injection t5 with hV t6
            injection t6 with hH t7
            injection t7 with hR t8
            injection t8 with hP t9
            injection t9 with hN _
            cases hT
            cases hA
            cases hC
            cases hK
            cases hU
            cases hV
            cases hH
            cases hR
            cases hP
            cases hN
            rfl

instance largeModelAttentionGateNontrivial : Nontrivial LargeModelAttentionGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LargeModelAttentionGateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LargeModelAttentionGateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LargeModelAttentionGateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  largeModelAttentionGateChapterTasteGate

theorem LargeModelAttentionGateTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      largeModelAttentionGateDecodeBHist (largeModelAttentionGateEncodeBHist h) = h) ∧
      (∀ x : LargeModelAttentionGateUp,
        largeModelAttentionGateFromEventFlow (largeModelAttentionGateToEventFlow x) = some x) ∧
        (∀ x y : LargeModelAttentionGateUp,
          largeModelAttentionGateToEventFlow x = largeModelAttentionGateToEventFlow y →
            x = y) ∧
          largeModelAttentionGateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact largeModelAttentionGateDecode_encode_bhist
  · constructor
    · exact largeModelAttentionGate_round_trip
    · constructor
      · intro x y heq
        exact largeModelAttentionGateToEventFlow_injective heq
      · rfl

end BEDC.Derived.LargeModelAttentionGateUp
