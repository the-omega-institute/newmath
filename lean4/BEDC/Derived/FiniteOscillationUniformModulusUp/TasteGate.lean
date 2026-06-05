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

private theorem finiteOscillationUniformModulusDecodeEncodeBHist :
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

private def finiteOscillationUniformModulusRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => finiteOscillationUniformModulusRawAt n rest

private def finiteOscillationUniformModulusLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => finiteOscillationUniformModulusLengthEq n rest

def finiteOscillationUniformModulusFromEventFlow :
    EventFlow → Option FiniteOscillationUniformModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match finiteOscillationUniformModulusLengthEq 10 flow with
      | true =>
          some
            (FiniteOscillationUniformModulusUp.mk
              (finiteOscillationUniformModulusDecodeBHist
                (finiteOscillationUniformModulusRawAt 0 flow))
              (finiteOscillationUniformModulusDecodeBHist
                (finiteOscillationUniformModulusRawAt 1 flow))
              (finiteOscillationUniformModulusDecodeBHist
                (finiteOscillationUniformModulusRawAt 2 flow))
              (finiteOscillationUniformModulusDecodeBHist
                (finiteOscillationUniformModulusRawAt 3 flow))
              (finiteOscillationUniformModulusDecodeBHist
                (finiteOscillationUniformModulusRawAt 4 flow))
              (finiteOscillationUniformModulusDecodeBHist
                (finiteOscillationUniformModulusRawAt 5 flow))
              (finiteOscillationUniformModulusDecodeBHist
                (finiteOscillationUniformModulusRawAt 6 flow))
              (finiteOscillationUniformModulusDecodeBHist
                (finiteOscillationUniformModulusRawAt 7 flow))
              (finiteOscillationUniformModulusDecodeBHist
                (finiteOscillationUniformModulusRawAt 8 flow))
              (finiteOscillationUniformModulusDecodeBHist
                (finiteOscillationUniformModulusRawAt 9 flow)))
      | false => none

private theorem finiteOscillationUniformModulus_round_trip :
    ∀ x : FiniteOscillationUniformModulusUp,
      finiteOscillationUniformModulusFromEventFlow
          (finiteOscillationUniformModulusToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
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
      rw [finiteOscillationUniformModulusDecodeEncodeBHist K,
        finiteOscillationUniformModulusDecodeEncodeBHist M,
        finiteOscillationUniformModulusDecodeEncodeBHist A,
        finiteOscillationUniformModulusDecodeEncodeBHist B,
        finiteOscillationUniformModulusDecodeEncodeBHist O,
        finiteOscillationUniformModulusDecodeEncodeBHist U,
        finiteOscillationUniformModulusDecodeEncodeBHist H,
        finiteOscillationUniformModulusDecodeEncodeBHist C,
        finiteOscillationUniformModulusDecodeEncodeBHist P,
        finiteOscillationUniformModulusDecodeEncodeBHist N]

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
    ⟨finiteOscillationUniformModulusDecodeEncodeBHist,
      finiteOscillationUniformModulus_round_trip,
      (fun _ _ heq => finiteOscillationUniformModulusToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FiniteOscillationUniformModulusUp
