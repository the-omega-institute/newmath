import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConstructiveDiniModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConstructiveDiniModulusUp : Type where
  | mk (K F L N Q W S R E G M H C P A : BHist) : ConstructiveDiniModulusUp
  deriving DecidableEq

def constructiveDiniModulusEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: constructiveDiniModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: constructiveDiniModulusEncodeBHist h

def constructiveDiniModulusDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (constructiveDiniModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (constructiveDiniModulusDecodeBHist tail)

private theorem ConstructiveDiniModulusTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      constructiveDiniModulusDecodeBHist (constructiveDiniModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def constructiveDiniModulusToEventFlow : ConstructiveDiniModulusUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ConstructiveDiniModulusUp.mk K F L N Q W S R E G M H C P A =>
      [constructiveDiniModulusEncodeBHist K,
        constructiveDiniModulusEncodeBHist F,
        constructiveDiniModulusEncodeBHist L,
        constructiveDiniModulusEncodeBHist N,
        constructiveDiniModulusEncodeBHist Q,
        constructiveDiniModulusEncodeBHist W,
        constructiveDiniModulusEncodeBHist S,
        constructiveDiniModulusEncodeBHist R,
        constructiveDiniModulusEncodeBHist E,
        constructiveDiniModulusEncodeBHist G,
        constructiveDiniModulusEncodeBHist M,
        constructiveDiniModulusEncodeBHist H,
        constructiveDiniModulusEncodeBHist C,
        constructiveDiniModulusEncodeBHist P,
        constructiveDiniModulusEncodeBHist A]

private def constructiveDiniModulusEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => constructiveDiniModulusEventAtDefault index rest

def constructiveDiniModulusFromEventFlow
    (ef : EventFlow) : Option ConstructiveDiniModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ConstructiveDiniModulusUp.mk
      (constructiveDiniModulusDecodeBHist (constructiveDiniModulusEventAtDefault 0 ef))
      (constructiveDiniModulusDecodeBHist (constructiveDiniModulusEventAtDefault 1 ef))
      (constructiveDiniModulusDecodeBHist (constructiveDiniModulusEventAtDefault 2 ef))
      (constructiveDiniModulusDecodeBHist (constructiveDiniModulusEventAtDefault 3 ef))
      (constructiveDiniModulusDecodeBHist (constructiveDiniModulusEventAtDefault 4 ef))
      (constructiveDiniModulusDecodeBHist (constructiveDiniModulusEventAtDefault 5 ef))
      (constructiveDiniModulusDecodeBHist (constructiveDiniModulusEventAtDefault 6 ef))
      (constructiveDiniModulusDecodeBHist (constructiveDiniModulusEventAtDefault 7 ef))
      (constructiveDiniModulusDecodeBHist (constructiveDiniModulusEventAtDefault 8 ef))
      (constructiveDiniModulusDecodeBHist (constructiveDiniModulusEventAtDefault 9 ef))
      (constructiveDiniModulusDecodeBHist (constructiveDiniModulusEventAtDefault 10 ef))
      (constructiveDiniModulusDecodeBHist (constructiveDiniModulusEventAtDefault 11 ef))
      (constructiveDiniModulusDecodeBHist (constructiveDiniModulusEventAtDefault 12 ef))
      (constructiveDiniModulusDecodeBHist (constructiveDiniModulusEventAtDefault 13 ef))
      (constructiveDiniModulusDecodeBHist (constructiveDiniModulusEventAtDefault 14 ef)))

private theorem ConstructiveDiniModulusTasteGate_single_carrier_alignment_round_trip
    (x : ConstructiveDiniModulusUp) :
    constructiveDiniModulusFromEventFlow (constructiveDiniModulusToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K F L N Q W S R E G M H C P A =>
      change
        some
          (ConstructiveDiniModulusUp.mk
            (constructiveDiniModulusDecodeBHist (constructiveDiniModulusEncodeBHist K))
            (constructiveDiniModulusDecodeBHist (constructiveDiniModulusEncodeBHist F))
            (constructiveDiniModulusDecodeBHist (constructiveDiniModulusEncodeBHist L))
            (constructiveDiniModulusDecodeBHist (constructiveDiniModulusEncodeBHist N))
            (constructiveDiniModulusDecodeBHist (constructiveDiniModulusEncodeBHist Q))
            (constructiveDiniModulusDecodeBHist (constructiveDiniModulusEncodeBHist W))
            (constructiveDiniModulusDecodeBHist (constructiveDiniModulusEncodeBHist S))
            (constructiveDiniModulusDecodeBHist (constructiveDiniModulusEncodeBHist R))
            (constructiveDiniModulusDecodeBHist (constructiveDiniModulusEncodeBHist E))
            (constructiveDiniModulusDecodeBHist (constructiveDiniModulusEncodeBHist G))
            (constructiveDiniModulusDecodeBHist (constructiveDiniModulusEncodeBHist M))
            (constructiveDiniModulusDecodeBHist (constructiveDiniModulusEncodeBHist H))
            (constructiveDiniModulusDecodeBHist (constructiveDiniModulusEncodeBHist C))
            (constructiveDiniModulusDecodeBHist (constructiveDiniModulusEncodeBHist P))
            (constructiveDiniModulusDecodeBHist (constructiveDiniModulusEncodeBHist A))) =
          some (ConstructiveDiniModulusUp.mk K F L N Q W S R E G M H C P A)
      rw [ConstructiveDiniModulusTasteGate_single_carrier_alignment_decode_encode K,
        ConstructiveDiniModulusTasteGate_single_carrier_alignment_decode_encode F,
        ConstructiveDiniModulusTasteGate_single_carrier_alignment_decode_encode L,
        ConstructiveDiniModulusTasteGate_single_carrier_alignment_decode_encode N,
        ConstructiveDiniModulusTasteGate_single_carrier_alignment_decode_encode Q,
        ConstructiveDiniModulusTasteGate_single_carrier_alignment_decode_encode W,
        ConstructiveDiniModulusTasteGate_single_carrier_alignment_decode_encode S,
        ConstructiveDiniModulusTasteGate_single_carrier_alignment_decode_encode R,
        ConstructiveDiniModulusTasteGate_single_carrier_alignment_decode_encode E,
        ConstructiveDiniModulusTasteGate_single_carrier_alignment_decode_encode G,
        ConstructiveDiniModulusTasteGate_single_carrier_alignment_decode_encode M,
        ConstructiveDiniModulusTasteGate_single_carrier_alignment_decode_encode H,
        ConstructiveDiniModulusTasteGate_single_carrier_alignment_decode_encode C,
        ConstructiveDiniModulusTasteGate_single_carrier_alignment_decode_encode P,
        ConstructiveDiniModulusTasteGate_single_carrier_alignment_decode_encode A]

private theorem ConstructiveDiniModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ConstructiveDiniModulusUp} :
    constructiveDiniModulusToEventFlow x = constructiveDiniModulusToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      constructiveDiniModulusFromEventFlow (constructiveDiniModulusToEventFlow x) =
        constructiveDiniModulusFromEventFlow (constructiveDiniModulusToEventFlow y) :=
    congrArg constructiveDiniModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ConstructiveDiniModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ConstructiveDiniModulusTasteGate_single_carrier_alignment_round_trip y)))

instance constructiveDiniModulusBHistCarrier : BHistCarrier ConstructiveDiniModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := constructiveDiniModulusToEventFlow
  fromEventFlow := constructiveDiniModulusFromEventFlow

instance constructiveDiniModulusChapterTasteGate :
    ChapterTasteGate ConstructiveDiniModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change constructiveDiniModulusFromEventFlow (constructiveDiniModulusToEventFlow x) =
      some x
    exact ConstructiveDiniModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ConstructiveDiniModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem ConstructiveDiniModulusTasteGate_single_carrier_alignment :
    (forall h : BHist,
      constructiveDiniModulusDecodeBHist (constructiveDiniModulusEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ConstructiveDiniModulusUp) ∧
        Nonempty (ChapterTasteGate ConstructiveDiniModulusUp) ∧
          constructiveDiniModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨ConstructiveDiniModulusTasteGate_single_carrier_alignment_decode_encode,
      ⟨constructiveDiniModulusBHistCarrier⟩,
      ⟨constructiveDiniModulusChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.ConstructiveDiniModulusUp
