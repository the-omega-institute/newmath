import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TotallyBoundedCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TotallyBoundedCompletionUp : Type where
  | mk
      (source net refinement basis embedding completion separated extension transport provenance
        localName : BHist) :
      TotallyBoundedCompletionUp
  deriving DecidableEq

def totallyBoundedCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: totallyBoundedCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: totallyBoundedCompletionEncodeBHist h

def totallyBoundedCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (totallyBoundedCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (totallyBoundedCompletionDecodeBHist tail)

private theorem totallyBoundedCompletionDecode_encode_bhist :
    ∀ h : BHist,
      totallyBoundedCompletionDecodeBHist (totallyBoundedCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def totallyBoundedCompletionFields : TotallyBoundedCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TotallyBoundedCompletionUp.mk source net refinement basis embedding completion separated
      extension transport provenance localName =>
      [source, net, refinement, basis, embedding, completion, separated, extension, transport,
        provenance, localName]

def totallyBoundedCompletionToEventFlow : TotallyBoundedCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TotallyBoundedCompletionUp.mk source net refinement basis embedding completion separated
      extension transport provenance localName =>
      [[BMark.b0],
        totallyBoundedCompletionEncodeBHist source,
        [BMark.b1, BMark.b0],
        totallyBoundedCompletionEncodeBHist net,
        [BMark.b1, BMark.b1, BMark.b0],
        totallyBoundedCompletionEncodeBHist refinement,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        totallyBoundedCompletionEncodeBHist basis,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        totallyBoundedCompletionEncodeBHist embedding,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        totallyBoundedCompletionEncodeBHist completion,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        totallyBoundedCompletionEncodeBHist separated,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        totallyBoundedCompletionEncodeBHist extension,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        totallyBoundedCompletionEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        totallyBoundedCompletionEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        totallyBoundedCompletionEncodeBHist localName]

private def totallyBoundedCompletionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => totallyBoundedCompletionEventAtDefault index rest

def totallyBoundedCompletionFromEventFlow : EventFlow → Option TotallyBoundedCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (TotallyBoundedCompletionUp.mk
          (totallyBoundedCompletionDecodeBHist
            (totallyBoundedCompletionEventAtDefault 1 ef))
          (totallyBoundedCompletionDecodeBHist
            (totallyBoundedCompletionEventAtDefault 3 ef))
          (totallyBoundedCompletionDecodeBHist
            (totallyBoundedCompletionEventAtDefault 5 ef))
          (totallyBoundedCompletionDecodeBHist
            (totallyBoundedCompletionEventAtDefault 7 ef))
          (totallyBoundedCompletionDecodeBHist
            (totallyBoundedCompletionEventAtDefault 9 ef))
          (totallyBoundedCompletionDecodeBHist
            (totallyBoundedCompletionEventAtDefault 11 ef))
          (totallyBoundedCompletionDecodeBHist
            (totallyBoundedCompletionEventAtDefault 13 ef))
          (totallyBoundedCompletionDecodeBHist
            (totallyBoundedCompletionEventAtDefault 15 ef))
          (totallyBoundedCompletionDecodeBHist
            (totallyBoundedCompletionEventAtDefault 17 ef))
          (totallyBoundedCompletionDecodeBHist
            (totallyBoundedCompletionEventAtDefault 19 ef))
          (totallyBoundedCompletionDecodeBHist
            (totallyBoundedCompletionEventAtDefault 21 ef)))

private theorem totallyBoundedCompletion_round_trip :
    ∀ x : TotallyBoundedCompletionUp,
      totallyBoundedCompletionFromEventFlow (totallyBoundedCompletionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source net refinement basis embedding completion separated extension transport provenance
      localName =>
      change
        some
          (TotallyBoundedCompletionUp.mk
            (totallyBoundedCompletionDecodeBHist (totallyBoundedCompletionEncodeBHist source))
            (totallyBoundedCompletionDecodeBHist (totallyBoundedCompletionEncodeBHist net))
            (totallyBoundedCompletionDecodeBHist
              (totallyBoundedCompletionEncodeBHist refinement))
            (totallyBoundedCompletionDecodeBHist (totallyBoundedCompletionEncodeBHist basis))
            (totallyBoundedCompletionDecodeBHist
              (totallyBoundedCompletionEncodeBHist embedding))
            (totallyBoundedCompletionDecodeBHist
              (totallyBoundedCompletionEncodeBHist completion))
            (totallyBoundedCompletionDecodeBHist
              (totallyBoundedCompletionEncodeBHist separated))
            (totallyBoundedCompletionDecodeBHist
              (totallyBoundedCompletionEncodeBHist extension))
            (totallyBoundedCompletionDecodeBHist
              (totallyBoundedCompletionEncodeBHist transport))
            (totallyBoundedCompletionDecodeBHist
              (totallyBoundedCompletionEncodeBHist provenance))
            (totallyBoundedCompletionDecodeBHist
              (totallyBoundedCompletionEncodeBHist localName))) =
          some
            (TotallyBoundedCompletionUp.mk source net refinement basis embedding completion
              separated extension transport provenance localName)
      rw [totallyBoundedCompletionDecode_encode_bhist source,
        totallyBoundedCompletionDecode_encode_bhist net,
        totallyBoundedCompletionDecode_encode_bhist refinement,
        totallyBoundedCompletionDecode_encode_bhist basis,
        totallyBoundedCompletionDecode_encode_bhist embedding,
        totallyBoundedCompletionDecode_encode_bhist completion,
        totallyBoundedCompletionDecode_encode_bhist separated,
        totallyBoundedCompletionDecode_encode_bhist extension,
        totallyBoundedCompletionDecode_encode_bhist transport,
        totallyBoundedCompletionDecode_encode_bhist provenance,
        totallyBoundedCompletionDecode_encode_bhist localName]

private theorem totallyBoundedCompletionToEventFlow_injective
    {x y : TotallyBoundedCompletionUp} :
    totallyBoundedCompletionToEventFlow x = totallyBoundedCompletionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      totallyBoundedCompletionFromEventFlow (totallyBoundedCompletionToEventFlow x) =
        totallyBoundedCompletionFromEventFlow (totallyBoundedCompletionToEventFlow y) :=
    congrArg totallyBoundedCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (totallyBoundedCompletion_round_trip x).symm
      (Eq.trans hread (totallyBoundedCompletion_round_trip y)))

instance totallyBoundedCompletionBHistCarrier :
    BHistCarrier TotallyBoundedCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := totallyBoundedCompletionToEventFlow
  fromEventFlow := totallyBoundedCompletionFromEventFlow

instance totallyBoundedCompletionChapterTasteGate :
    ChapterTasteGate TotallyBoundedCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      totallyBoundedCompletionFromEventFlow (totallyBoundedCompletionToEventFlow x) =
        some x
    exact totallyBoundedCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (totallyBoundedCompletionToEventFlow_injective heq)

namespace TasteGate

theorem TotallyBoundedCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      totallyBoundedCompletionDecodeBHist (totallyBoundedCompletionEncodeBHist h) = h) ∧
      (∀ x : TotallyBoundedCompletionUp,
        totallyBoundedCompletionFromEventFlow (totallyBoundedCompletionToEventFlow x) =
          some x) ∧
        (∀ x y : TotallyBoundedCompletionUp,
          totallyBoundedCompletionToEventFlow x =
            totallyBoundedCompletionToEventFlow y → x = y) ∧
          totallyBoundedCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  · constructor
    · intro x
      cases x with
      | mk source net refinement basis embedding completion separated extension transport
          provenance localName =>
          change
            some
              (TotallyBoundedCompletionUp.mk
                (totallyBoundedCompletionDecodeBHist
                  (totallyBoundedCompletionEncodeBHist source))
                (totallyBoundedCompletionDecodeBHist
                  (totallyBoundedCompletionEncodeBHist net))
                (totallyBoundedCompletionDecodeBHist
                  (totallyBoundedCompletionEncodeBHist refinement))
                (totallyBoundedCompletionDecodeBHist
                  (totallyBoundedCompletionEncodeBHist basis))
                (totallyBoundedCompletionDecodeBHist
                  (totallyBoundedCompletionEncodeBHist embedding))
                (totallyBoundedCompletionDecodeBHist
                  (totallyBoundedCompletionEncodeBHist completion))
                (totallyBoundedCompletionDecodeBHist
                  (totallyBoundedCompletionEncodeBHist separated))
                (totallyBoundedCompletionDecodeBHist
                  (totallyBoundedCompletionEncodeBHist extension))
                (totallyBoundedCompletionDecodeBHist
                  (totallyBoundedCompletionEncodeBHist transport))
                (totallyBoundedCompletionDecodeBHist
                  (totallyBoundedCompletionEncodeBHist provenance))
                (totallyBoundedCompletionDecodeBHist
                  (totallyBoundedCompletionEncodeBHist localName))) =
              some
                (TotallyBoundedCompletionUp.mk source net refinement basis embedding
                  completion separated extension transport provenance localName)
          rw [totallyBoundedCompletionDecode_encode_bhist source,
            totallyBoundedCompletionDecode_encode_bhist net,
            totallyBoundedCompletionDecode_encode_bhist refinement,
            totallyBoundedCompletionDecode_encode_bhist basis,
            totallyBoundedCompletionDecode_encode_bhist embedding,
            totallyBoundedCompletionDecode_encode_bhist completion,
            totallyBoundedCompletionDecode_encode_bhist separated,
            totallyBoundedCompletionDecode_encode_bhist extension,
            totallyBoundedCompletionDecode_encode_bhist transport,
            totallyBoundedCompletionDecode_encode_bhist provenance,
            totallyBoundedCompletionDecode_encode_bhist localName]
    · constructor
      · intro x y heq
        have hread :
            totallyBoundedCompletionFromEventFlow (totallyBoundedCompletionToEventFlow x) =
              totallyBoundedCompletionFromEventFlow (totallyBoundedCompletionToEventFlow y) :=
          congrArg totallyBoundedCompletionFromEventFlow heq
        exact Option.some.inj
          (Eq.trans (totallyBoundedCompletion_round_trip x).symm
            (Eq.trans hread (totallyBoundedCompletion_round_trip y)))
      · rfl

end TasteGate

end BEDC.Derived.TotallyBoundedCompletionUp
