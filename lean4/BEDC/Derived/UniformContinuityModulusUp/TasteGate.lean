import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformContinuityModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformContinuityModulusUp : Type where
  | mk (X Y F epsilon delta M H C P N : BHist) : UniformContinuityModulusUp
  deriving DecidableEq

def uniformContinuityModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformContinuityModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformContinuityModulusEncodeBHist h

def uniformContinuityModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformContinuityModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformContinuityModulusDecodeBHist tail)

private theorem uniformContinuityModulusDecode_encode :
    ∀ h : BHist,
      uniformContinuityModulusDecodeBHist (uniformContinuityModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformContinuityModulusToEventFlow : UniformContinuityModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | UniformContinuityModulusUp.mk X Y F epsilon delta M H C P N =>
      [uniformContinuityModulusEncodeBHist X,
        uniformContinuityModulusEncodeBHist Y,
        uniformContinuityModulusEncodeBHist F,
        uniformContinuityModulusEncodeBHist epsilon,
        uniformContinuityModulusEncodeBHist delta,
        uniformContinuityModulusEncodeBHist M,
        uniformContinuityModulusEncodeBHist H,
        uniformContinuityModulusEncodeBHist C,
        uniformContinuityModulusEncodeBHist P,
        uniformContinuityModulusEncodeBHist N]

private def uniformContinuityModulusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformContinuityModulusEventAtDefault index rest

def uniformContinuityModulusFromEventFlow : EventFlow → Option UniformContinuityModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
      some
        (UniformContinuityModulusUp.mk
          (uniformContinuityModulusDecodeBHist (uniformContinuityModulusEventAtDefault 0 ef))
          (uniformContinuityModulusDecodeBHist (uniformContinuityModulusEventAtDefault 1 ef))
          (uniformContinuityModulusDecodeBHist (uniformContinuityModulusEventAtDefault 2 ef))
          (uniformContinuityModulusDecodeBHist (uniformContinuityModulusEventAtDefault 3 ef))
          (uniformContinuityModulusDecodeBHist (uniformContinuityModulusEventAtDefault 4 ef))
          (uniformContinuityModulusDecodeBHist (uniformContinuityModulusEventAtDefault 5 ef))
          (uniformContinuityModulusDecodeBHist (uniformContinuityModulusEventAtDefault 6 ef))
          (uniformContinuityModulusDecodeBHist (uniformContinuityModulusEventAtDefault 7 ef))
          (uniformContinuityModulusDecodeBHist (uniformContinuityModulusEventAtDefault 8 ef))
          (uniformContinuityModulusDecodeBHist (uniformContinuityModulusEventAtDefault 9 ef)))

private theorem uniformContinuityModulus_round_trip :
    ∀ x : UniformContinuityModulusUp,
      uniformContinuityModulusFromEventFlow (uniformContinuityModulusToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y F epsilon delta M H C P N =>
      change
        some
          (UniformContinuityModulusUp.mk
            (uniformContinuityModulusDecodeBHist (uniformContinuityModulusEncodeBHist X))
            (uniformContinuityModulusDecodeBHist (uniformContinuityModulusEncodeBHist Y))
            (uniformContinuityModulusDecodeBHist (uniformContinuityModulusEncodeBHist F))
            (uniformContinuityModulusDecodeBHist
              (uniformContinuityModulusEncodeBHist epsilon))
            (uniformContinuityModulusDecodeBHist
              (uniformContinuityModulusEncodeBHist delta))
            (uniformContinuityModulusDecodeBHist (uniformContinuityModulusEncodeBHist M))
            (uniformContinuityModulusDecodeBHist (uniformContinuityModulusEncodeBHist H))
            (uniformContinuityModulusDecodeBHist (uniformContinuityModulusEncodeBHist C))
            (uniformContinuityModulusDecodeBHist (uniformContinuityModulusEncodeBHist P))
            (uniformContinuityModulusDecodeBHist (uniformContinuityModulusEncodeBHist N))) =
          some (UniformContinuityModulusUp.mk X Y F epsilon delta M H C P N)
      rw [uniformContinuityModulusDecode_encode X,
        uniformContinuityModulusDecode_encode Y,
        uniformContinuityModulusDecode_encode F,
        uniformContinuityModulusDecode_encode epsilon,
        uniformContinuityModulusDecode_encode delta,
        uniformContinuityModulusDecode_encode M,
        uniformContinuityModulusDecode_encode H,
        uniformContinuityModulusDecode_encode C,
        uniformContinuityModulusDecode_encode P,
        uniformContinuityModulusDecode_encode N]

private theorem uniformContinuityModulusToEventFlow_injective
    {x y : UniformContinuityModulusUp} :
    uniformContinuityModulusToEventFlow x = uniformContinuityModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformContinuityModulusFromEventFlow (uniformContinuityModulusToEventFlow x) =
        uniformContinuityModulusFromEventFlow (uniformContinuityModulusToEventFlow y) :=
    congrArg uniformContinuityModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (uniformContinuityModulus_round_trip x).symm
      (Eq.trans hread (uniformContinuityModulus_round_trip y)))

def uniformContinuityModulusFields : UniformContinuityModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformContinuityModulusUp.mk X Y F epsilon delta M H C P N =>
      [X, Y, F, epsilon, delta, M, H, C, P, N]

private theorem uniformContinuityModulus_field_faithful :
    ∀ x y : UniformContinuityModulusUp,
      uniformContinuityModulusFields x = uniformContinuityModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 Y1 F1 epsilon1 delta1 M1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 Y2 F2 epsilon2 delta2 M2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance uniformContinuityModulusBHistCarrier :
    BHistCarrier UniformContinuityModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformContinuityModulusToEventFlow
  fromEventFlow := uniformContinuityModulusFromEventFlow

instance uniformContinuityModulusChapterTasteGate :
    ChapterTasteGate UniformContinuityModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformContinuityModulusFromEventFlow (uniformContinuityModulusToEventFlow x) =
        some x
    exact uniformContinuityModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformContinuityModulusToEventFlow_injective heq)

instance uniformContinuityModulusFieldFaithful :
    FieldFaithful UniformContinuityModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformContinuityModulusFields
  field_faithful := uniformContinuityModulus_field_faithful

theorem UniformContinuityModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      uniformContinuityModulusDecodeBHist (uniformContinuityModulusEncodeBHist h) = h) ∧
      (∀ x : UniformContinuityModulusUp,
        uniformContinuityModulusFromEventFlow (uniformContinuityModulusToEventFlow x) =
          some x) ∧
      (∀ x y : UniformContinuityModulusUp,
        uniformContinuityModulusToEventFlow x = uniformContinuityModulusToEventFlow y →
          x = y) ∧
      uniformContinuityModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨uniformContinuityModulusDecode_encode,
      uniformContinuityModulus_round_trip,
      fun _ _ heq => uniformContinuityModulusToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.UniformContinuityModulusUp
