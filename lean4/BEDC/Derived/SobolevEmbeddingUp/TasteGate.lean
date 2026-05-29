import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SobolevEmbeddingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SobolevEmbeddingUp : Type where
  | mk (D S N E T R L P : BHist) : SobolevEmbeddingUp
  deriving DecidableEq

def sobolevEmbeddingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sobolevEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sobolevEmbeddingEncodeBHist h

def sobolevEmbeddingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sobolevEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sobolevEmbeddingDecodeBHist tail)

private theorem sobolevEmbeddingDecode_encode :
    ∀ h : BHist, sobolevEmbeddingDecodeBHist (sobolevEmbeddingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sobolevEmbeddingToEventFlow : SobolevEmbeddingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SobolevEmbeddingUp.mk D S N E T R L P =>
      [sobolevEmbeddingEncodeBHist D,
        sobolevEmbeddingEncodeBHist S,
        sobolevEmbeddingEncodeBHist N,
        sobolevEmbeddingEncodeBHist E,
        sobolevEmbeddingEncodeBHist T,
        sobolevEmbeddingEncodeBHist R,
        sobolevEmbeddingEncodeBHist L,
        sobolevEmbeddingEncodeBHist P]

private def sobolevEmbeddingEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => sobolevEmbeddingEventAtDefault index rest

def sobolevEmbeddingFromEventFlow : EventFlow → Option SobolevEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
      some
        (SobolevEmbeddingUp.mk
          (sobolevEmbeddingDecodeBHist (sobolevEmbeddingEventAtDefault 0 ef))
          (sobolevEmbeddingDecodeBHist (sobolevEmbeddingEventAtDefault 1 ef))
          (sobolevEmbeddingDecodeBHist (sobolevEmbeddingEventAtDefault 2 ef))
          (sobolevEmbeddingDecodeBHist (sobolevEmbeddingEventAtDefault 3 ef))
          (sobolevEmbeddingDecodeBHist (sobolevEmbeddingEventAtDefault 4 ef))
          (sobolevEmbeddingDecodeBHist (sobolevEmbeddingEventAtDefault 5 ef))
          (sobolevEmbeddingDecodeBHist (sobolevEmbeddingEventAtDefault 6 ef))
          (sobolevEmbeddingDecodeBHist (sobolevEmbeddingEventAtDefault 7 ef)))

private theorem sobolevEmbedding_round_trip :
    ∀ x : SobolevEmbeddingUp,
      sobolevEmbeddingFromEventFlow (sobolevEmbeddingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S N E T R L P =>
      change
        some
          (SobolevEmbeddingUp.mk
            (sobolevEmbeddingDecodeBHist (sobolevEmbeddingEncodeBHist D))
            (sobolevEmbeddingDecodeBHist (sobolevEmbeddingEncodeBHist S))
            (sobolevEmbeddingDecodeBHist (sobolevEmbeddingEncodeBHist N))
            (sobolevEmbeddingDecodeBHist (sobolevEmbeddingEncodeBHist E))
            (sobolevEmbeddingDecodeBHist (sobolevEmbeddingEncodeBHist T))
            (sobolevEmbeddingDecodeBHist (sobolevEmbeddingEncodeBHist R))
            (sobolevEmbeddingDecodeBHist (sobolevEmbeddingEncodeBHist L))
            (sobolevEmbeddingDecodeBHist (sobolevEmbeddingEncodeBHist P))) =
          some (SobolevEmbeddingUp.mk D S N E T R L P)
      rw [sobolevEmbeddingDecode_encode D,
        sobolevEmbeddingDecode_encode S,
        sobolevEmbeddingDecode_encode N,
        sobolevEmbeddingDecode_encode E,
        sobolevEmbeddingDecode_encode T,
        sobolevEmbeddingDecode_encode R,
        sobolevEmbeddingDecode_encode L,
        sobolevEmbeddingDecode_encode P]

private theorem sobolevEmbeddingToEventFlow_injective {x y : SobolevEmbeddingUp} :
    sobolevEmbeddingToEventFlow x = sobolevEmbeddingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sobolevEmbeddingFromEventFlow (sobolevEmbeddingToEventFlow x) =
        sobolevEmbeddingFromEventFlow (sobolevEmbeddingToEventFlow y) :=
    congrArg sobolevEmbeddingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (sobolevEmbedding_round_trip x).symm
      (Eq.trans hread (sobolevEmbedding_round_trip y)))

def sobolevEmbeddingFields : SobolevEmbeddingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SobolevEmbeddingUp.mk D S N E T R L P => [D, S, N, E, T, R, L, P]

private theorem sobolevEmbedding_field_faithful :
    ∀ x y : SobolevEmbeddingUp, sobolevEmbeddingFields x = sobolevEmbeddingFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D1 S1 N1 E1 T1 R1 L1 P1 =>
      cases y with
      | mk D2 S2 N2 E2 T2 R2 L2 P2 =>
          cases hfields
          rfl

instance sobolevEmbeddingBHistCarrier : BHistCarrier SobolevEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sobolevEmbeddingToEventFlow
  fromEventFlow := sobolevEmbeddingFromEventFlow

instance sobolevEmbeddingChapterTasteGate : ChapterTasteGate SobolevEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sobolevEmbeddingFromEventFlow (sobolevEmbeddingToEventFlow x) = some x
    exact sobolevEmbedding_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (sobolevEmbeddingToEventFlow_injective heq)

instance sobolevEmbeddingFieldFaithful : FieldFaithful SobolevEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := sobolevEmbeddingFields
  field_faithful := sobolevEmbedding_field_faithful

theorem SobolevEmbeddingTasteGate_single_carrier_alignment :
    (∀ h : BHist, sobolevEmbeddingDecodeBHist (sobolevEmbeddingEncodeBHist h) = h) ∧
      (∀ x : SobolevEmbeddingUp,
        sobolevEmbeddingFromEventFlow (sobolevEmbeddingToEventFlow x) = some x) ∧
      (∀ x y : SobolevEmbeddingUp,
        sobolevEmbeddingToEventFlow x = sobolevEmbeddingToEventFlow y → x = y) ∧
      sobolevEmbeddingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨sobolevEmbeddingDecode_encode,
      sobolevEmbedding_round_trip,
      fun _ _ heq => sobolevEmbeddingToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.SobolevEmbeddingUp
