import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteOscillationUniformModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteOscillationUniformModulusUp : Type where
  | mk (K M A B O U H C P N : BHist) : FiniteOscillationUniformModulusUp
  deriving DecidableEq

def finiteOscillationUniformModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteOscillationUniformModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteOscillationUniformModulusEncodeBHist h

def finiteOscillationUniformModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteOscillationUniformModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteOscillationUniformModulusDecodeBHist tail)

private theorem finiteOscillationUniformModulus_decode_encode :
    ∀ h : BHist,
      finiteOscillationUniformModulusDecodeBHist
          (finiteOscillationUniformModulusEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteOscillationUniformModulusFields :
    FiniteOscillationUniformModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteOscillationUniformModulusUp.mk K M A B O U H C P N =>
      [K, M, A, B, O, U, H, C, P, N]

def finiteOscillationUniformModulusToEventFlow :
    FiniteOscillationUniformModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (finiteOscillationUniformModulusFields x).map
        finiteOscillationUniformModulusEncodeBHist

private def finiteOscillationUniformModulusEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      finiteOscillationUniformModulusEventAtDefault index rest

def finiteOscillationUniformModulusFromEventFlow
    (ef : EventFlow) : Option FiniteOscillationUniformModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteOscillationUniformModulusUp.mk
      (finiteOscillationUniformModulusDecodeBHist
        (finiteOscillationUniformModulusEventAtDefault 0 ef))
      (finiteOscillationUniformModulusDecodeBHist
        (finiteOscillationUniformModulusEventAtDefault 1 ef))
      (finiteOscillationUniformModulusDecodeBHist
        (finiteOscillationUniformModulusEventAtDefault 2 ef))
      (finiteOscillationUniformModulusDecodeBHist
        (finiteOscillationUniformModulusEventAtDefault 3 ef))
      (finiteOscillationUniformModulusDecodeBHist
        (finiteOscillationUniformModulusEventAtDefault 4 ef))
      (finiteOscillationUniformModulusDecodeBHist
        (finiteOscillationUniformModulusEventAtDefault 5 ef))
      (finiteOscillationUniformModulusDecodeBHist
        (finiteOscillationUniformModulusEventAtDefault 6 ef))
      (finiteOscillationUniformModulusDecodeBHist
        (finiteOscillationUniformModulusEventAtDefault 7 ef))
      (finiteOscillationUniformModulusDecodeBHist
        (finiteOscillationUniformModulusEventAtDefault 8 ef))
      (finiteOscillationUniformModulusDecodeBHist
        (finiteOscillationUniformModulusEventAtDefault 9 ef)))

private theorem finiteOscillationUniformModulus_round_trip
    (x : FiniteOscillationUniformModulusUp) :
    finiteOscillationUniformModulusFromEventFlow
        (finiteOscillationUniformModulusToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K M A B O U H C P N =>
      change
        some
          (FiniteOscillationUniformModulusUp.mk
            (finiteOscillationUniformModulusDecodeBHist
              (finiteOscillationUniformModulusEncodeBHist K))
            (finiteOscillationUniformModulusDecodeBHist
              (finiteOscillationUniformModulusEncodeBHist M))
            (finiteOscillationUniformModulusDecodeBHist
              (finiteOscillationUniformModulusEncodeBHist A))
            (finiteOscillationUniformModulusDecodeBHist
              (finiteOscillationUniformModulusEncodeBHist B))
            (finiteOscillationUniformModulusDecodeBHist
              (finiteOscillationUniformModulusEncodeBHist O))
            (finiteOscillationUniformModulusDecodeBHist
              (finiteOscillationUniformModulusEncodeBHist U))
            (finiteOscillationUniformModulusDecodeBHist
              (finiteOscillationUniformModulusEncodeBHist H))
            (finiteOscillationUniformModulusDecodeBHist
              (finiteOscillationUniformModulusEncodeBHist C))
            (finiteOscillationUniformModulusDecodeBHist
              (finiteOscillationUniformModulusEncodeBHist P))
            (finiteOscillationUniformModulusDecodeBHist
              (finiteOscillationUniformModulusEncodeBHist N))) =
          some (FiniteOscillationUniformModulusUp.mk K M A B O U H C P N)
      rw [finiteOscillationUniformModulus_decode_encode K,
        finiteOscillationUniformModulus_decode_encode M,
        finiteOscillationUniformModulus_decode_encode A,
        finiteOscillationUniformModulus_decode_encode B,
        finiteOscillationUniformModulus_decode_encode O,
        finiteOscillationUniformModulus_decode_encode U,
        finiteOscillationUniformModulus_decode_encode H,
        finiteOscillationUniformModulus_decode_encode C,
        finiteOscillationUniformModulus_decode_encode P,
        finiteOscillationUniformModulus_decode_encode N]

private theorem finiteOscillationUniformModulusToEventFlow_injective
    {x y : FiniteOscillationUniformModulusUp} :
    finiteOscillationUniformModulusToEventFlow x =
        finiteOscillationUniformModulusToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteOscillationUniformModulusFromEventFlow
          (finiteOscillationUniformModulusToEventFlow x) =
        finiteOscillationUniformModulusFromEventFlow
          (finiteOscillationUniformModulusToEventFlow y) :=
    congrArg finiteOscillationUniformModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteOscillationUniformModulus_round_trip x).symm
      (Eq.trans hread (finiteOscillationUniformModulus_round_trip y)))

private theorem finiteOscillationUniformModulus_fields_faithful :
    ∀ x y : FiniteOscillationUniformModulusUp,
      finiteOscillationUniformModulusFields x =
          finiteOscillationUniformModulusFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K1 M1 A1 B1 O1 U1 H1 C1 P1 N1 =>
      cases y with
      | mk K2 M2 A2 B2 O2 U2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance finiteOscillationUniformModulusBHistCarrier :
    BHistCarrier FiniteOscillationUniformModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteOscillationUniformModulusToEventFlow
  fromEventFlow := finiteOscillationUniformModulusFromEventFlow

instance finiteOscillationUniformModulusChapterTasteGate :
    ChapterTasteGate FiniteOscillationUniformModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteOscillationUniformModulusFromEventFlow
          (finiteOscillationUniformModulusToEventFlow x) =
        some x
    exact finiteOscillationUniformModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteOscillationUniformModulusToEventFlow_injective heq)

instance finiteOscillationUniformModulusFieldFaithful :
    FieldFaithful FiniteOscillationUniformModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteOscillationUniformModulusFields
  field_faithful := finiteOscillationUniformModulus_fields_faithful

instance finiteOscillationUniformModulusNontrivial :
    BEDC.Meta.TasteGate.Nontrivial FiniteOscillationUniformModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteOscillationUniformModulusUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      FiniteOscillationUniformModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteOscillationUniformModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteOscillationUniformModulusChapterTasteGate

def taste_gate_witness : FieldFaithful FiniteOscillationUniformModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteOscillationUniformModulusFieldFaithful

theorem FiniteOscillationUniformModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        finiteOscillationUniformModulusDecodeBHist
            (finiteOscillationUniformModulusEncodeBHist h) = h) ∧
      (∀ x : FiniteOscillationUniformModulusUp,
        finiteOscillationUniformModulusFromEventFlow
            (finiteOscillationUniformModulusToEventFlow x) = some x) ∧
        (∀ x y : FiniteOscillationUniformModulusUp,
          finiteOscillationUniformModulusToEventFlow x =
              finiteOscillationUniformModulusToEventFlow y →
            x = y) ∧
          finiteOscillationUniformModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨finiteOscillationUniformModulus_decode_encode,
      finiteOscillationUniformModulus_round_trip,
      (fun _ _ heq => finiteOscillationUniformModulusToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FiniteOscillationUniformModulusUp
