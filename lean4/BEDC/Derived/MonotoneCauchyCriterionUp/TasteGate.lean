import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MonotoneCauchyCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MonotoneCauchyCriterionUp : Type where
  | mk (B S T M D L R E H C P N : BHist) : MonotoneCauchyCriterionUp
  deriving DecidableEq

def monotoneCauchyCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: monotoneCauchyCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: monotoneCauchyCriterionEncodeBHist h

def monotoneCauchyCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (monotoneCauchyCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (monotoneCauchyCriterionDecodeBHist tail)

private theorem monotoneCauchyCriterionDecode_encode_bhist :
    ∀ h : BHist,
      monotoneCauchyCriterionDecodeBHist (monotoneCauchyCriterionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def monotoneCauchyCriterionFields : MonotoneCauchyCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MonotoneCauchyCriterionUp.mk B S T M D L R E H C P N =>
      [B, S, T, M, D, L, R, E, H, C, P, N]

def monotoneCauchyCriterionToEventFlow : MonotoneCauchyCriterionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (monotoneCauchyCriterionFields x).map monotoneCauchyCriterionEncodeBHist

private def monotoneCauchyCriterionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => monotoneCauchyCriterionEventAt index rest

def monotoneCauchyCriterionFromEventFlow
    (ef : EventFlow) : Option MonotoneCauchyCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MonotoneCauchyCriterionUp.mk
      (monotoneCauchyCriterionDecodeBHist (monotoneCauchyCriterionEventAt 0 ef))
      (monotoneCauchyCriterionDecodeBHist (monotoneCauchyCriterionEventAt 1 ef))
      (monotoneCauchyCriterionDecodeBHist (monotoneCauchyCriterionEventAt 2 ef))
      (monotoneCauchyCriterionDecodeBHist (monotoneCauchyCriterionEventAt 3 ef))
      (monotoneCauchyCriterionDecodeBHist (monotoneCauchyCriterionEventAt 4 ef))
      (monotoneCauchyCriterionDecodeBHist (monotoneCauchyCriterionEventAt 5 ef))
      (monotoneCauchyCriterionDecodeBHist (monotoneCauchyCriterionEventAt 6 ef))
      (monotoneCauchyCriterionDecodeBHist (monotoneCauchyCriterionEventAt 7 ef))
      (monotoneCauchyCriterionDecodeBHist (monotoneCauchyCriterionEventAt 8 ef))
      (monotoneCauchyCriterionDecodeBHist (monotoneCauchyCriterionEventAt 9 ef))
      (monotoneCauchyCriterionDecodeBHist (monotoneCauchyCriterionEventAt 10 ef))
      (monotoneCauchyCriterionDecodeBHist (monotoneCauchyCriterionEventAt 11 ef)))

private theorem monotoneCauchyCriterion_round_trip
    (x : MonotoneCauchyCriterionUp) :
    monotoneCauchyCriterionFromEventFlow (monotoneCauchyCriterionToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B S T M D L R E H C P N =>
      change
        some
          (MonotoneCauchyCriterionUp.mk
            (monotoneCauchyCriterionDecodeBHist
              (monotoneCauchyCriterionEncodeBHist B))
            (monotoneCauchyCriterionDecodeBHist
              (monotoneCauchyCriterionEncodeBHist S))
            (monotoneCauchyCriterionDecodeBHist
              (monotoneCauchyCriterionEncodeBHist T))
            (monotoneCauchyCriterionDecodeBHist
              (monotoneCauchyCriterionEncodeBHist M))
            (monotoneCauchyCriterionDecodeBHist
              (monotoneCauchyCriterionEncodeBHist D))
            (monotoneCauchyCriterionDecodeBHist
              (monotoneCauchyCriterionEncodeBHist L))
            (monotoneCauchyCriterionDecodeBHist
              (monotoneCauchyCriterionEncodeBHist R))
            (monotoneCauchyCriterionDecodeBHist
              (monotoneCauchyCriterionEncodeBHist E))
            (monotoneCauchyCriterionDecodeBHist
              (monotoneCauchyCriterionEncodeBHist H))
            (monotoneCauchyCriterionDecodeBHist
              (monotoneCauchyCriterionEncodeBHist C))
            (monotoneCauchyCriterionDecodeBHist
              (monotoneCauchyCriterionEncodeBHist P))
            (monotoneCauchyCriterionDecodeBHist
              (monotoneCauchyCriterionEncodeBHist N))) =
          some (MonotoneCauchyCriterionUp.mk B S T M D L R E H C P N)
      rw [monotoneCauchyCriterionDecode_encode_bhist B,
        monotoneCauchyCriterionDecode_encode_bhist S,
        monotoneCauchyCriterionDecode_encode_bhist T,
        monotoneCauchyCriterionDecode_encode_bhist M,
        monotoneCauchyCriterionDecode_encode_bhist D,
        monotoneCauchyCriterionDecode_encode_bhist L,
        monotoneCauchyCriterionDecode_encode_bhist R,
        monotoneCauchyCriterionDecode_encode_bhist E,
        monotoneCauchyCriterionDecode_encode_bhist H,
        monotoneCauchyCriterionDecode_encode_bhist C,
        monotoneCauchyCriterionDecode_encode_bhist P,
        monotoneCauchyCriterionDecode_encode_bhist N]

private theorem monotoneCauchyCriterionToEventFlow_injective
    {x y : MonotoneCauchyCriterionUp} :
    monotoneCauchyCriterionToEventFlow x =
        monotoneCauchyCriterionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      monotoneCauchyCriterionFromEventFlow (monotoneCauchyCriterionToEventFlow x) =
        monotoneCauchyCriterionFromEventFlow (monotoneCauchyCriterionToEventFlow y) :=
    congrArg monotoneCauchyCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (monotoneCauchyCriterion_round_trip x).symm
      (Eq.trans hread (monotoneCauchyCriterion_round_trip y)))

instance monotoneCauchyCriterionBHistCarrier :
    BHistCarrier MonotoneCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := monotoneCauchyCriterionToEventFlow
  fromEventFlow := monotoneCauchyCriterionFromEventFlow

instance monotoneCauchyCriterionChapterTasteGate :
    ChapterTasteGate MonotoneCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      monotoneCauchyCriterionFromEventFlow (monotoneCauchyCriterionToEventFlow x) =
        some x
    exact monotoneCauchyCriterion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (monotoneCauchyCriterionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate MonotoneCauchyCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  monotoneCauchyCriterionChapterTasteGate

theorem MonotoneCauchyCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      monotoneCauchyCriterionDecodeBHist (monotoneCauchyCriterionEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier MonotoneCauchyCriterionUp) ∧
        Nonempty (ChapterTasteGate MonotoneCauchyCriterionUp) ∧
          monotoneCauchyCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨monotoneCauchyCriterionDecode_encode_bhist,
      ⟨monotoneCauchyCriterionBHistCarrier⟩,
      ⟨monotoneCauchyCriterionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.MonotoneCauchyCriterionUp
