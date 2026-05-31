import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactUniformFiniteNetRealizationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactUniformFiniteNetRealizationUp : Type where
  | mk : (C M F B L R U T H D P N : BHist) →
      CompactUniformFiniteNetRealizationUp
  deriving DecidableEq

def compactUniformFiniteNetRealizationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactUniformFiniteNetRealizationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactUniformFiniteNetRealizationEncodeBHist h

def compactUniformFiniteNetRealizationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (compactUniformFiniteNetRealizationDecodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (compactUniformFiniteNetRealizationDecodeBHist tail)

private theorem compactUniformFiniteNetRealizationDecode_encode :
    ∀ h : BHist,
      compactUniformFiniteNetRealizationDecodeBHist
        (compactUniformFiniteNetRealizationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactUniformFiniteNetRealizationFields :
    CompactUniformFiniteNetRealizationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactUniformFiniteNetRealizationUp.mk C M F B L R U T H D P N =>
      [C, M, F, B, L, R, U, T, H, D, P, N]

def compactUniformFiniteNetRealizationToEventFlow :
    CompactUniformFiniteNetRealizationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactUniformFiniteNetRealizationFields x).map
      compactUniformFiniteNetRealizationEncodeBHist

private def compactUniformFiniteNetRealizationEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      compactUniformFiniteNetRealizationEventAtDefault index rest

def compactUniformFiniteNetRealizationFromEventFlow
    (ef : EventFlow) : Option CompactUniformFiniteNetRealizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactUniformFiniteNetRealizationUp.mk
      (compactUniformFiniteNetRealizationDecodeBHist
        (compactUniformFiniteNetRealizationEventAtDefault 0 ef))
      (compactUniformFiniteNetRealizationDecodeBHist
        (compactUniformFiniteNetRealizationEventAtDefault 1 ef))
      (compactUniformFiniteNetRealizationDecodeBHist
        (compactUniformFiniteNetRealizationEventAtDefault 2 ef))
      (compactUniformFiniteNetRealizationDecodeBHist
        (compactUniformFiniteNetRealizationEventAtDefault 3 ef))
      (compactUniformFiniteNetRealizationDecodeBHist
        (compactUniformFiniteNetRealizationEventAtDefault 4 ef))
      (compactUniformFiniteNetRealizationDecodeBHist
        (compactUniformFiniteNetRealizationEventAtDefault 5 ef))
      (compactUniformFiniteNetRealizationDecodeBHist
        (compactUniformFiniteNetRealizationEventAtDefault 6 ef))
      (compactUniformFiniteNetRealizationDecodeBHist
        (compactUniformFiniteNetRealizationEventAtDefault 7 ef))
      (compactUniformFiniteNetRealizationDecodeBHist
        (compactUniformFiniteNetRealizationEventAtDefault 8 ef))
      (compactUniformFiniteNetRealizationDecodeBHist
        (compactUniformFiniteNetRealizationEventAtDefault 9 ef))
      (compactUniformFiniteNetRealizationDecodeBHist
        (compactUniformFiniteNetRealizationEventAtDefault 10 ef))
      (compactUniformFiniteNetRealizationDecodeBHist
        (compactUniformFiniteNetRealizationEventAtDefault 11 ef)))

private theorem compactUniformFiniteNetRealization_round_trip :
    ∀ x : CompactUniformFiniteNetRealizationUp,
      compactUniformFiniteNetRealizationFromEventFlow
        (compactUniformFiniteNetRealizationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk C M F B L R U T H D P N =>
      change
        some
          (CompactUniformFiniteNetRealizationUp.mk
            (compactUniformFiniteNetRealizationDecodeBHist
              (compactUniformFiniteNetRealizationEncodeBHist C))
            (compactUniformFiniteNetRealizationDecodeBHist
              (compactUniformFiniteNetRealizationEncodeBHist M))
            (compactUniformFiniteNetRealizationDecodeBHist
              (compactUniformFiniteNetRealizationEncodeBHist F))
            (compactUniformFiniteNetRealizationDecodeBHist
              (compactUniformFiniteNetRealizationEncodeBHist B))
            (compactUniformFiniteNetRealizationDecodeBHist
              (compactUniformFiniteNetRealizationEncodeBHist L))
            (compactUniformFiniteNetRealizationDecodeBHist
              (compactUniformFiniteNetRealizationEncodeBHist R))
            (compactUniformFiniteNetRealizationDecodeBHist
              (compactUniformFiniteNetRealizationEncodeBHist U))
            (compactUniformFiniteNetRealizationDecodeBHist
              (compactUniformFiniteNetRealizationEncodeBHist T))
            (compactUniformFiniteNetRealizationDecodeBHist
              (compactUniformFiniteNetRealizationEncodeBHist H))
            (compactUniformFiniteNetRealizationDecodeBHist
              (compactUniformFiniteNetRealizationEncodeBHist D))
            (compactUniformFiniteNetRealizationDecodeBHist
              (compactUniformFiniteNetRealizationEncodeBHist P))
            (compactUniformFiniteNetRealizationDecodeBHist
              (compactUniformFiniteNetRealizationEncodeBHist N))) =
          some (CompactUniformFiniteNetRealizationUp.mk C M F B L R U T H D P N)
      rw [compactUniformFiniteNetRealizationDecode_encode C,
        compactUniformFiniteNetRealizationDecode_encode M,
        compactUniformFiniteNetRealizationDecode_encode F,
        compactUniformFiniteNetRealizationDecode_encode B,
        compactUniformFiniteNetRealizationDecode_encode L,
        compactUniformFiniteNetRealizationDecode_encode R,
        compactUniformFiniteNetRealizationDecode_encode U,
        compactUniformFiniteNetRealizationDecode_encode T,
        compactUniformFiniteNetRealizationDecode_encode H,
        compactUniformFiniteNetRealizationDecode_encode D,
        compactUniformFiniteNetRealizationDecode_encode P,
        compactUniformFiniteNetRealizationDecode_encode N]

private theorem compactUniformFiniteNetRealizationToEventFlow_injective
    {x y : CompactUniformFiniteNetRealizationUp} :
    compactUniformFiniteNetRealizationToEventFlow x =
      compactUniformFiniteNetRealizationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactUniformFiniteNetRealizationFromEventFlow
          (compactUniformFiniteNetRealizationToEventFlow x) =
        compactUniformFiniteNetRealizationFromEventFlow
          (compactUniformFiniteNetRealizationToEventFlow y) :=
    congrArg compactUniformFiniteNetRealizationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactUniformFiniteNetRealization_round_trip x).symm
      (Eq.trans hread (compactUniformFiniteNetRealization_round_trip y)))

instance compactUniformFiniteNetRealizationBHistCarrier :
    BHistCarrier CompactUniformFiniteNetRealizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactUniformFiniteNetRealizationToEventFlow
  fromEventFlow := compactUniformFiniteNetRealizationFromEventFlow

instance compactUniformFiniteNetRealizationChapterTasteGate :
    ChapterTasteGate CompactUniformFiniteNetRealizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactUniformFiniteNetRealizationFromEventFlow
        (compactUniformFiniteNetRealizationToEventFlow x) = some x
    exact compactUniformFiniteNetRealization_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactUniformFiniteNetRealizationToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CompactUniformFiniteNetRealizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactUniformFiniteNetRealizationChapterTasteGate

theorem CompactUniformFiniteNetRealizationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactUniformFiniteNetRealizationDecodeBHist
        (compactUniformFiniteNetRealizationEncodeBHist h) = h) ∧
      (∀ x : CompactUniformFiniteNetRealizationUp,
        compactUniformFiniteNetRealizationFromEventFlow
          (compactUniformFiniteNetRealizationToEventFlow x) = some x) ∧
      (∀ x y : CompactUniformFiniteNetRealizationUp,
        compactUniformFiniteNetRealizationToEventFlow x =
          compactUniformFiniteNetRealizationToEventFlow y → x = y) ∧
      compactUniformFiniteNetRealizationEncodeBHist BHist.Empty =
        ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨compactUniformFiniteNetRealizationDecode_encode,
      compactUniformFiniteNetRealization_round_trip,
      fun _ _ heq => compactUniformFiniteNetRealizationToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.CompactUniformFiniteNetRealizationUp
