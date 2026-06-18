import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConstructiveContractionModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConstructiveContractionModulusUp : Type where
  | mk (X F L Q W R E H C P N : BHist) : ConstructiveContractionModulusUp
  deriving DecidableEq

def constructiveContractionModulusEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: constructiveContractionModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: constructiveContractionModulusEncodeBHist h

def constructiveContractionModulusDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (constructiveContractionModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (constructiveContractionModulusDecodeBHist tail)

private theorem ConstructiveContractionModulusTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      constructiveContractionModulusDecodeBHist
        (constructiveContractionModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def constructiveContractionModulusToEventFlow :
    ConstructiveContractionModulusUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ConstructiveContractionModulusUp.mk X F L Q W R E H C P N =>
      [[BMark.b0],
        constructiveContractionModulusEncodeBHist X,
        [BMark.b1, BMark.b0],
        constructiveContractionModulusEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b0],
        constructiveContractionModulusEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        constructiveContractionModulusEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        constructiveContractionModulusEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        constructiveContractionModulusEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        constructiveContractionModulusEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        constructiveContractionModulusEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        constructiveContractionModulusEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        constructiveContractionModulusEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        constructiveContractionModulusEncodeBHist N]

private def constructiveContractionModulusEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      constructiveContractionModulusEventAtDefault index rest

def constructiveContractionModulusFromEventFlow
    (ef : EventFlow) : Option ConstructiveContractionModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ConstructiveContractionModulusUp.mk
      (constructiveContractionModulusDecodeBHist
        (constructiveContractionModulusEventAtDefault 1 ef))
      (constructiveContractionModulusDecodeBHist
        (constructiveContractionModulusEventAtDefault 3 ef))
      (constructiveContractionModulusDecodeBHist
        (constructiveContractionModulusEventAtDefault 5 ef))
      (constructiveContractionModulusDecodeBHist
        (constructiveContractionModulusEventAtDefault 7 ef))
      (constructiveContractionModulusDecodeBHist
        (constructiveContractionModulusEventAtDefault 9 ef))
      (constructiveContractionModulusDecodeBHist
        (constructiveContractionModulusEventAtDefault 11 ef))
      (constructiveContractionModulusDecodeBHist
        (constructiveContractionModulusEventAtDefault 13 ef))
      (constructiveContractionModulusDecodeBHist
        (constructiveContractionModulusEventAtDefault 15 ef))
      (constructiveContractionModulusDecodeBHist
        (constructiveContractionModulusEventAtDefault 17 ef))
      (constructiveContractionModulusDecodeBHist
        (constructiveContractionModulusEventAtDefault 19 ef))
      (constructiveContractionModulusDecodeBHist
        (constructiveContractionModulusEventAtDefault 21 ef)))

private theorem ConstructiveContractionModulusTasteGate_single_carrier_alignment_round_trip :
    forall x : ConstructiveContractionModulusUp,
      constructiveContractionModulusFromEventFlow
        (constructiveContractionModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X F L Q W R E H C P N =>
      change
        some
          (ConstructiveContractionModulusUp.mk
            (constructiveContractionModulusDecodeBHist
              (constructiveContractionModulusEncodeBHist X))
            (constructiveContractionModulusDecodeBHist
              (constructiveContractionModulusEncodeBHist F))
            (constructiveContractionModulusDecodeBHist
              (constructiveContractionModulusEncodeBHist L))
            (constructiveContractionModulusDecodeBHist
              (constructiveContractionModulusEncodeBHist Q))
            (constructiveContractionModulusDecodeBHist
              (constructiveContractionModulusEncodeBHist W))
            (constructiveContractionModulusDecodeBHist
              (constructiveContractionModulusEncodeBHist R))
            (constructiveContractionModulusDecodeBHist
              (constructiveContractionModulusEncodeBHist E))
            (constructiveContractionModulusDecodeBHist
              (constructiveContractionModulusEncodeBHist H))
            (constructiveContractionModulusDecodeBHist
              (constructiveContractionModulusEncodeBHist C))
            (constructiveContractionModulusDecodeBHist
              (constructiveContractionModulusEncodeBHist P))
            (constructiveContractionModulusDecodeBHist
              (constructiveContractionModulusEncodeBHist N))) =
          some (ConstructiveContractionModulusUp.mk X F L Q W R E H C P N)
      rw [ConstructiveContractionModulusTasteGate_single_carrier_alignment_decode_encode X,
        ConstructiveContractionModulusTasteGate_single_carrier_alignment_decode_encode F,
        ConstructiveContractionModulusTasteGate_single_carrier_alignment_decode_encode L,
        ConstructiveContractionModulusTasteGate_single_carrier_alignment_decode_encode Q,
        ConstructiveContractionModulusTasteGate_single_carrier_alignment_decode_encode W,
        ConstructiveContractionModulusTasteGate_single_carrier_alignment_decode_encode R,
        ConstructiveContractionModulusTasteGate_single_carrier_alignment_decode_encode E,
        ConstructiveContractionModulusTasteGate_single_carrier_alignment_decode_encode H,
        ConstructiveContractionModulusTasteGate_single_carrier_alignment_decode_encode C,
        ConstructiveContractionModulusTasteGate_single_carrier_alignment_decode_encode P,
        ConstructiveContractionModulusTasteGate_single_carrier_alignment_decode_encode N]

private theorem ConstructiveContractionModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ConstructiveContractionModulusUp} :
    constructiveContractionModulusToEventFlow x =
        constructiveContractionModulusToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      constructiveContractionModulusFromEventFlow
          (constructiveContractionModulusToEventFlow x) =
        constructiveContractionModulusFromEventFlow
          (constructiveContractionModulusToEventFlow y) :=
    congrArg constructiveContractionModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ConstructiveContractionModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ConstructiveContractionModulusTasteGate_single_carrier_alignment_round_trip y)))

instance constructiveContractionModulusBHistCarrier :
    BHistCarrier ConstructiveContractionModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := constructiveContractionModulusToEventFlow
  fromEventFlow := constructiveContractionModulusFromEventFlow

instance constructiveContractionModulusChapterTasteGate :
    ChapterTasteGate ConstructiveContractionModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      constructiveContractionModulusFromEventFlow
        (constructiveContractionModulusToEventFlow x) = some x
    exact ConstructiveContractionModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ConstructiveContractionModulusTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def taste_gate : ChapterTasteGate ConstructiveContractionModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  constructiveContractionModulusChapterTasteGate

theorem ConstructiveContractionModulusTasteGate_single_carrier_alignment :
    (forall x : ConstructiveContractionModulusUp,
      BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
      Nonempty (BHistCarrier ConstructiveContractionModulusUp) ∧
        Nonempty (ChapterTasteGate ConstructiveContractionModulusUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    change
      constructiveContractionModulusFromEventFlow
        (constructiveContractionModulusToEventFlow x) = some x
    exact ConstructiveContractionModulusTasteGate_single_carrier_alignment_round_trip x
  · constructor
    · exact ⟨constructiveContractionModulusBHistCarrier⟩
    · exact ⟨constructiveContractionModulusChapterTasteGate⟩

end BEDC.Derived.ConstructiveContractionModulusUp
