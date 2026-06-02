import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformEmbeddingCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformEmbeddingCompletionUp : Type where
  | mk (M S U Q R T W A H C P N : BHist) : UniformEmbeddingCompletionUp
  deriving DecidableEq

def uniformEmbeddingCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformEmbeddingCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformEmbeddingCompletionEncodeBHist h

def uniformEmbeddingCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformEmbeddingCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformEmbeddingCompletionDecodeBHist tail)

private theorem UniformEmbeddingCompletionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      uniformEmbeddingCompletionDecodeBHist
        (uniformEmbeddingCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformEmbeddingCompletionFields : UniformEmbeddingCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformEmbeddingCompletionUp.mk M S U Q R T W A H C P N =>
      [M, S, U, Q, R, T, W, A, H, C, P, N]

def uniformEmbeddingCompletionToEventFlow : UniformEmbeddingCompletionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (uniformEmbeddingCompletionFields x).map uniformEmbeddingCompletionEncodeBHist

private def uniformEmbeddingCompletionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformEmbeddingCompletionEventAtDefault index rest

def uniformEmbeddingCompletionFromEventFlow
    (ef : EventFlow) : Option UniformEmbeddingCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformEmbeddingCompletionUp.mk
      (uniformEmbeddingCompletionDecodeBHist (uniformEmbeddingCompletionEventAtDefault 0 ef))
      (uniformEmbeddingCompletionDecodeBHist (uniformEmbeddingCompletionEventAtDefault 1 ef))
      (uniformEmbeddingCompletionDecodeBHist (uniformEmbeddingCompletionEventAtDefault 2 ef))
      (uniformEmbeddingCompletionDecodeBHist (uniformEmbeddingCompletionEventAtDefault 3 ef))
      (uniformEmbeddingCompletionDecodeBHist (uniformEmbeddingCompletionEventAtDefault 4 ef))
      (uniformEmbeddingCompletionDecodeBHist (uniformEmbeddingCompletionEventAtDefault 5 ef))
      (uniformEmbeddingCompletionDecodeBHist (uniformEmbeddingCompletionEventAtDefault 6 ef))
      (uniformEmbeddingCompletionDecodeBHist (uniformEmbeddingCompletionEventAtDefault 7 ef))
      (uniformEmbeddingCompletionDecodeBHist (uniformEmbeddingCompletionEventAtDefault 8 ef))
      (uniformEmbeddingCompletionDecodeBHist (uniformEmbeddingCompletionEventAtDefault 9 ef))
      (uniformEmbeddingCompletionDecodeBHist (uniformEmbeddingCompletionEventAtDefault 10 ef))
      (uniformEmbeddingCompletionDecodeBHist (uniformEmbeddingCompletionEventAtDefault 11 ef)))

private theorem UniformEmbeddingCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UniformEmbeddingCompletionUp,
      uniformEmbeddingCompletionFromEventFlow
        (uniformEmbeddingCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M S U Q R T W A H C P N =>
      change
        some
          (UniformEmbeddingCompletionUp.mk
            (uniformEmbeddingCompletionDecodeBHist (uniformEmbeddingCompletionEncodeBHist M))
            (uniformEmbeddingCompletionDecodeBHist (uniformEmbeddingCompletionEncodeBHist S))
            (uniformEmbeddingCompletionDecodeBHist (uniformEmbeddingCompletionEncodeBHist U))
            (uniformEmbeddingCompletionDecodeBHist (uniformEmbeddingCompletionEncodeBHist Q))
            (uniformEmbeddingCompletionDecodeBHist (uniformEmbeddingCompletionEncodeBHist R))
            (uniformEmbeddingCompletionDecodeBHist (uniformEmbeddingCompletionEncodeBHist T))
            (uniformEmbeddingCompletionDecodeBHist (uniformEmbeddingCompletionEncodeBHist W))
            (uniformEmbeddingCompletionDecodeBHist (uniformEmbeddingCompletionEncodeBHist A))
            (uniformEmbeddingCompletionDecodeBHist (uniformEmbeddingCompletionEncodeBHist H))
            (uniformEmbeddingCompletionDecodeBHist (uniformEmbeddingCompletionEncodeBHist C))
            (uniformEmbeddingCompletionDecodeBHist (uniformEmbeddingCompletionEncodeBHist P))
            (uniformEmbeddingCompletionDecodeBHist (uniformEmbeddingCompletionEncodeBHist N))) =
          some (UniformEmbeddingCompletionUp.mk M S U Q R T W A H C P N)
      rw [UniformEmbeddingCompletionTasteGate_single_carrier_alignment_decode M,
        UniformEmbeddingCompletionTasteGate_single_carrier_alignment_decode S,
        UniformEmbeddingCompletionTasteGate_single_carrier_alignment_decode U,
        UniformEmbeddingCompletionTasteGate_single_carrier_alignment_decode Q,
        UniformEmbeddingCompletionTasteGate_single_carrier_alignment_decode R,
        UniformEmbeddingCompletionTasteGate_single_carrier_alignment_decode T,
        UniformEmbeddingCompletionTasteGate_single_carrier_alignment_decode W,
        UniformEmbeddingCompletionTasteGate_single_carrier_alignment_decode A,
        UniformEmbeddingCompletionTasteGate_single_carrier_alignment_decode H,
        UniformEmbeddingCompletionTasteGate_single_carrier_alignment_decode C,
        UniformEmbeddingCompletionTasteGate_single_carrier_alignment_decode P,
        UniformEmbeddingCompletionTasteGate_single_carrier_alignment_decode N]

private theorem UniformEmbeddingCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformEmbeddingCompletionUp} :
    uniformEmbeddingCompletionToEventFlow x = uniformEmbeddingCompletionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformEmbeddingCompletionFromEventFlow (uniformEmbeddingCompletionToEventFlow x) =
        uniformEmbeddingCompletionFromEventFlow (uniformEmbeddingCompletionToEventFlow y) :=
    congrArg uniformEmbeddingCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (UniformEmbeddingCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (UniformEmbeddingCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance uniformEmbeddingCompletionBHistCarrier : BHistCarrier UniformEmbeddingCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformEmbeddingCompletionToEventFlow
  fromEventFlow := uniformEmbeddingCompletionFromEventFlow

instance uniformEmbeddingCompletionChapterTasteGate :
    ChapterTasteGate UniformEmbeddingCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformEmbeddingCompletionFromEventFlow (uniformEmbeddingCompletionToEventFlow x) = some x
    exact UniformEmbeddingCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (UniformEmbeddingCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem UniformEmbeddingCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      uniformEmbeddingCompletionDecodeBHist
        (uniformEmbeddingCompletionEncodeBHist h) = h) ∧
      (∀ x : UniformEmbeddingCompletionUp,
        uniformEmbeddingCompletionFromEventFlow (uniformEmbeddingCompletionToEventFlow x) =
          some x) ∧
        (∀ x y : UniformEmbeddingCompletionUp,
          uniformEmbeddingCompletionToEventFlow x =
            uniformEmbeddingCompletionToEventFlow y → x = y) ∧
          uniformEmbeddingCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨UniformEmbeddingCompletionTasteGate_single_carrier_alignment_decode,
      UniformEmbeddingCompletionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        UniformEmbeddingCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.UniformEmbeddingCompletionUp
