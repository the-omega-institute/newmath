import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopFanModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopFanModulusUp : Type where
  | mk (F A B S Q D R U H C P N : BHist) : BishopFanModulusUp
  deriving DecidableEq

def bishopFanModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopFanModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopFanModulusEncodeBHist h

def bishopFanModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopFanModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopFanModulusDecodeBHist tail)

private theorem BishopFanModulusUpTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def bishopFanModulusFields : BishopFanModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopFanModulusUp.mk F A B S Q D R U H C P N =>
      [F, A, B, S, Q, D, R, U, H, C, P, N]

def bishopFanModulusToEventFlow : BishopFanModulusUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => List.map bishopFanModulusEncodeBHist (bishopFanModulusFields x)

private def bishopFanModulusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopFanModulusEventAtDefault index rest

def bishopFanModulusFromEventFlow (ef : EventFlow) : Option BishopFanModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopFanModulusUp.mk
      (bishopFanModulusDecodeBHist (bishopFanModulusEventAtDefault 0 ef))
      (bishopFanModulusDecodeBHist (bishopFanModulusEventAtDefault 1 ef))
      (bishopFanModulusDecodeBHist (bishopFanModulusEventAtDefault 2 ef))
      (bishopFanModulusDecodeBHist (bishopFanModulusEventAtDefault 3 ef))
      (bishopFanModulusDecodeBHist (bishopFanModulusEventAtDefault 4 ef))
      (bishopFanModulusDecodeBHist (bishopFanModulusEventAtDefault 5 ef))
      (bishopFanModulusDecodeBHist (bishopFanModulusEventAtDefault 6 ef))
      (bishopFanModulusDecodeBHist (bishopFanModulusEventAtDefault 7 ef))
      (bishopFanModulusDecodeBHist (bishopFanModulusEventAtDefault 8 ef))
      (bishopFanModulusDecodeBHist (bishopFanModulusEventAtDefault 9 ef))
      (bishopFanModulusDecodeBHist (bishopFanModulusEventAtDefault 10 ef))
      (bishopFanModulusDecodeBHist (bishopFanModulusEventAtDefault 11 ef)))

private theorem BishopFanModulusUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopFanModulusUp,
      bishopFanModulusFromEventFlow (bishopFanModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F A B S Q D R U H C P N =>
      change
        some
          (BishopFanModulusUp.mk
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist F))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist A))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist B))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist S))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist Q))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist D))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist R))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist U))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist H))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist C))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist P))
            (bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist N))) =
          some (BishopFanModulusUp.mk F A B S Q D R U H C P N)
      rw [BishopFanModulusUpTasteGate_single_carrier_alignment_decode_encode F,
        BishopFanModulusUpTasteGate_single_carrier_alignment_decode_encode A,
        BishopFanModulusUpTasteGate_single_carrier_alignment_decode_encode B,
        BishopFanModulusUpTasteGate_single_carrier_alignment_decode_encode S,
        BishopFanModulusUpTasteGate_single_carrier_alignment_decode_encode Q,
        BishopFanModulusUpTasteGate_single_carrier_alignment_decode_encode D,
        BishopFanModulusUpTasteGate_single_carrier_alignment_decode_encode R,
        BishopFanModulusUpTasteGate_single_carrier_alignment_decode_encode U,
        BishopFanModulusUpTasteGate_single_carrier_alignment_decode_encode H,
        BishopFanModulusUpTasteGate_single_carrier_alignment_decode_encode C,
        BishopFanModulusUpTasteGate_single_carrier_alignment_decode_encode P,
        BishopFanModulusUpTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopFanModulusUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopFanModulusUp} :
    bishopFanModulusToEventFlow x = bishopFanModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopFanModulusFromEventFlow (bishopFanModulusToEventFlow x) =
        bishopFanModulusFromEventFlow (bishopFanModulusToEventFlow y) :=
    congrArg bishopFanModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopFanModulusUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BishopFanModulusUpTasteGate_single_carrier_alignment_round_trip y)))

private theorem BishopFanModulusUpTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : BishopFanModulusUp, bishopFanModulusFields x = bishopFanModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 A1 B1 S1 Q1 D1 R1 U1 H1 C1 P1 N1 =>
      cases y with
      | mk F2 A2 B2 S2 Q2 D2 R2 U2 H2 C2 P2 N2 =>
          injection hfields with hF tail0
          injection tail0 with hA tail1
          injection tail1 with hB tail2
          injection tail2 with hS tail3
          injection tail3 with hQ tail4
          injection tail4 with hD tail5
          injection tail5 with hR tail6
          injection tail6 with hU tail7
          injection tail7 with hH tail8
          injection tail8 with hC tail9
          injection tail9 with hP tail10
          injection tail10 with hN _
          subst hF
          subst hA
          subst hB
          subst hS
          subst hQ
          subst hD
          subst hR
          subst hU
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance bishopFanModulusBHistCarrier : BHistCarrier BishopFanModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopFanModulusToEventFlow
  fromEventFlow := bishopFanModulusFromEventFlow

instance bishopFanModulusChapterTasteGate : ChapterTasteGate BishopFanModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopFanModulusFromEventFlow (bishopFanModulusToEventFlow x) = some x
    exact BishopFanModulusUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopFanModulusUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance bishopFanModulusFieldFaithful : FieldFaithful BishopFanModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopFanModulusFields
  field_faithful := BishopFanModulusUpTasteGate_single_carrier_alignment_fields_faithful

instance bishopFanModulusNontrivial : Nontrivial BishopFanModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopFanModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopFanModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BishopFanModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopFanModulusChapterTasteGate

def taste_gate_witness : FieldFaithful BishopFanModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopFanModulusFieldFaithful

theorem BishopFanModulusUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopFanModulusDecodeBHist (bishopFanModulusEncodeBHist h) = h) ∧
      (∀ x : BishopFanModulusUp,
        bishopFanModulusToEventFlow x =
          List.map bishopFanModulusEncodeBHist (bishopFanModulusFields x)) ∧
        (∀ x y : BishopFanModulusUp, bishopFanModulusFields x = bishopFanModulusFields y ->
          x = y) ∧
          (∃ x y : BishopFanModulusUp, x ≠ y) ∧
            bishopFanModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact BishopFanModulusUpTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · intro x
      rfl
    · constructor
      · exact BishopFanModulusUpTasteGate_single_carrier_alignment_fields_faithful
      · constructor
        · exact
            ⟨BishopFanModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty,
              BishopFanModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty,
              by
                intro h
                cases h⟩
        · rfl

end BEDC.Derived.BishopFanModulusUp
