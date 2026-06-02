import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DenseEmbeddingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DenseEmbeddingUp : Type where
  | mk (S T D W C H P N : BHist) : DenseEmbeddingUp
  deriving DecidableEq

def denseEmbeddingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: denseEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: denseEmbeddingEncodeBHist h

def denseEmbeddingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (denseEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (denseEmbeddingDecodeBHist tail)

private theorem DenseEmbeddingTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, denseEmbeddingDecodeBHist (denseEmbeddingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def denseEmbeddingFields : DenseEmbeddingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DenseEmbeddingUp.mk S T D W C H P N => [S, T, D, W, C, H, P, N]

def denseEmbeddingToEventFlow : DenseEmbeddingUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (denseEmbeddingFields x).map denseEmbeddingEncodeBHist

private def denseEmbeddingEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => denseEmbeddingEventAtDefault index rest

def denseEmbeddingFromEventFlow (ef : EventFlow) : Option DenseEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DenseEmbeddingUp.mk
      (denseEmbeddingDecodeBHist (denseEmbeddingEventAtDefault 0 ef))
      (denseEmbeddingDecodeBHist (denseEmbeddingEventAtDefault 1 ef))
      (denseEmbeddingDecodeBHist (denseEmbeddingEventAtDefault 2 ef))
      (denseEmbeddingDecodeBHist (denseEmbeddingEventAtDefault 3 ef))
      (denseEmbeddingDecodeBHist (denseEmbeddingEventAtDefault 4 ef))
      (denseEmbeddingDecodeBHist (denseEmbeddingEventAtDefault 5 ef))
      (denseEmbeddingDecodeBHist (denseEmbeddingEventAtDefault 6 ef))
      (denseEmbeddingDecodeBHist (denseEmbeddingEventAtDefault 7 ef)))

private theorem denseEmbedding_round_trip :
    ∀ x : DenseEmbeddingUp,
      denseEmbeddingFromEventFlow (denseEmbeddingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T D W C H P N =>
      change
        some
            (DenseEmbeddingUp.mk
              (denseEmbeddingDecodeBHist (denseEmbeddingEncodeBHist S))
              (denseEmbeddingDecodeBHist (denseEmbeddingEncodeBHist T))
              (denseEmbeddingDecodeBHist (denseEmbeddingEncodeBHist D))
              (denseEmbeddingDecodeBHist (denseEmbeddingEncodeBHist W))
              (denseEmbeddingDecodeBHist (denseEmbeddingEncodeBHist C))
              (denseEmbeddingDecodeBHist (denseEmbeddingEncodeBHist H))
              (denseEmbeddingDecodeBHist (denseEmbeddingEncodeBHist P))
              (denseEmbeddingDecodeBHist (denseEmbeddingEncodeBHist N))) =
          some (DenseEmbeddingUp.mk S T D W C H P N)
      rw [DenseEmbeddingTasteGate_single_carrier_alignment_decode S,
        DenseEmbeddingTasteGate_single_carrier_alignment_decode T,
        DenseEmbeddingTasteGate_single_carrier_alignment_decode D,
        DenseEmbeddingTasteGate_single_carrier_alignment_decode W,
        DenseEmbeddingTasteGate_single_carrier_alignment_decode C,
        DenseEmbeddingTasteGate_single_carrier_alignment_decode H,
        DenseEmbeddingTasteGate_single_carrier_alignment_decode P,
        DenseEmbeddingTasteGate_single_carrier_alignment_decode N]

private theorem denseEmbeddingToEventFlow_injective {x y : DenseEmbeddingUp} :
    denseEmbeddingToEventFlow x = denseEmbeddingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      denseEmbeddingFromEventFlow (denseEmbeddingToEventFlow x) =
        denseEmbeddingFromEventFlow (denseEmbeddingToEventFlow y) :=
    congrArg denseEmbeddingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (denseEmbedding_round_trip x).symm
      (Eq.trans hread (denseEmbedding_round_trip y)))

instance denseEmbeddingBHistCarrier : BHistCarrier DenseEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := denseEmbeddingToEventFlow
  fromEventFlow := denseEmbeddingFromEventFlow

instance denseEmbeddingChapterTasteGate : ChapterTasteGate DenseEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change denseEmbeddingFromEventFlow (denseEmbeddingToEventFlow x) = some x
    exact denseEmbedding_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (denseEmbeddingToEventFlow_injective heq)

instance denseEmbeddingFieldFaithful : FieldFaithful DenseEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := denseEmbeddingFields
  field_faithful := by
    intro x y h
    cases x with
    | mk S1 T1 D1 W1 C1 H1 P1 N1 =>
        cases y with
        | mk S2 T2 D2 W2 C2 H2 P2 N2 =>
            cases h
            rfl

def taste_gate : ChapterTasteGate DenseEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  denseEmbeddingChapterTasteGate

theorem DenseEmbeddingTasteGate_single_carrier_alignment :
    (∀ h : BHist, denseEmbeddingDecodeBHist (denseEmbeddingEncodeBHist h) = h) ∧
      (∀ x : DenseEmbeddingUp,
        denseEmbeddingFromEventFlow (denseEmbeddingToEventFlow x) = some x) ∧
        (∀ x y : DenseEmbeddingUp,
          denseEmbeddingToEventFlow x = denseEmbeddingToEventFlow y -> x = y) ∧
          denseEmbeddingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨DenseEmbeddingTasteGate_single_carrier_alignment_decode,
      denseEmbedding_round_trip,
      (fun _ _ heq => denseEmbeddingToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DenseEmbeddingUp
