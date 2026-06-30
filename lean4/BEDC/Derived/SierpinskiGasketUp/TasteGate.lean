import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SierpinskiGasketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SierpinskiGasketUp : Type where
  | mk (T I F A S W D R E H C P N : BHist) : SierpinskiGasketUp
  deriving DecidableEq

def sierpinskiGasketEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sierpinskiGasketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sierpinskiGasketEncodeBHist h

def sierpinskiGasketDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sierpinskiGasketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sierpinskiGasketDecodeBHist tail)

private theorem SierpinskiGasketTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, sierpinskiGasketDecodeBHist (sierpinskiGasketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sierpinskiGasketToEventFlow : SierpinskiGasketUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SierpinskiGasketUp.mk T I F A S W D R E H C P N =>
      [[BMark.b0],
        sierpinskiGasketEncodeBHist T,
        [BMark.b1, BMark.b0],
        sierpinskiGasketEncodeBHist I,
        [BMark.b1, BMark.b1, BMark.b0],
        sierpinskiGasketEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        sierpinskiGasketEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        sierpinskiGasketEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        sierpinskiGasketEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        sierpinskiGasketEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        sierpinskiGasketEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        sierpinskiGasketEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        sierpinskiGasketEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        sierpinskiGasketEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        sierpinskiGasketEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        sierpinskiGasketEncodeBHist N]

private def sierpinskiGasketEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => sierpinskiGasketEventAtDefault index rest

def sierpinskiGasketFromEventFlow (ef : EventFlow) : Option SierpinskiGasketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SierpinskiGasketUp.mk
      (sierpinskiGasketDecodeBHist (sierpinskiGasketEventAtDefault 1 ef))
      (sierpinskiGasketDecodeBHist (sierpinskiGasketEventAtDefault 3 ef))
      (sierpinskiGasketDecodeBHist (sierpinskiGasketEventAtDefault 5 ef))
      (sierpinskiGasketDecodeBHist (sierpinskiGasketEventAtDefault 7 ef))
      (sierpinskiGasketDecodeBHist (sierpinskiGasketEventAtDefault 9 ef))
      (sierpinskiGasketDecodeBHist (sierpinskiGasketEventAtDefault 11 ef))
      (sierpinskiGasketDecodeBHist (sierpinskiGasketEventAtDefault 13 ef))
      (sierpinskiGasketDecodeBHist (sierpinskiGasketEventAtDefault 15 ef))
      (sierpinskiGasketDecodeBHist (sierpinskiGasketEventAtDefault 17 ef))
      (sierpinskiGasketDecodeBHist (sierpinskiGasketEventAtDefault 19 ef))
      (sierpinskiGasketDecodeBHist (sierpinskiGasketEventAtDefault 21 ef))
      (sierpinskiGasketDecodeBHist (sierpinskiGasketEventAtDefault 23 ef))
      (sierpinskiGasketDecodeBHist (sierpinskiGasketEventAtDefault 25 ef)))

private theorem SierpinskiGasketTasteGate_single_carrier_alignment_round_trip :
    forall x : SierpinskiGasketUp,
      sierpinskiGasketFromEventFlow (sierpinskiGasketToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T I F A S W D R E H C P N =>
      change
        some
          (SierpinskiGasketUp.mk
            (sierpinskiGasketDecodeBHist (sierpinskiGasketEncodeBHist T))
            (sierpinskiGasketDecodeBHist (sierpinskiGasketEncodeBHist I))
            (sierpinskiGasketDecodeBHist (sierpinskiGasketEncodeBHist F))
            (sierpinskiGasketDecodeBHist (sierpinskiGasketEncodeBHist A))
            (sierpinskiGasketDecodeBHist (sierpinskiGasketEncodeBHist S))
            (sierpinskiGasketDecodeBHist (sierpinskiGasketEncodeBHist W))
            (sierpinskiGasketDecodeBHist (sierpinskiGasketEncodeBHist D))
            (sierpinskiGasketDecodeBHist (sierpinskiGasketEncodeBHist R))
            (sierpinskiGasketDecodeBHist (sierpinskiGasketEncodeBHist E))
            (sierpinskiGasketDecodeBHist (sierpinskiGasketEncodeBHist H))
            (sierpinskiGasketDecodeBHist (sierpinskiGasketEncodeBHist C))
            (sierpinskiGasketDecodeBHist (sierpinskiGasketEncodeBHist P))
            (sierpinskiGasketDecodeBHist (sierpinskiGasketEncodeBHist N))) =
          some (SierpinskiGasketUp.mk T I F A S W D R E H C P N)
      rw [SierpinskiGasketTasteGate_single_carrier_alignment_decode_encode T,
        SierpinskiGasketTasteGate_single_carrier_alignment_decode_encode I,
        SierpinskiGasketTasteGate_single_carrier_alignment_decode_encode F,
        SierpinskiGasketTasteGate_single_carrier_alignment_decode_encode A,
        SierpinskiGasketTasteGate_single_carrier_alignment_decode_encode S,
        SierpinskiGasketTasteGate_single_carrier_alignment_decode_encode W,
        SierpinskiGasketTasteGate_single_carrier_alignment_decode_encode D,
        SierpinskiGasketTasteGate_single_carrier_alignment_decode_encode R,
        SierpinskiGasketTasteGate_single_carrier_alignment_decode_encode E,
        SierpinskiGasketTasteGate_single_carrier_alignment_decode_encode H,
        SierpinskiGasketTasteGate_single_carrier_alignment_decode_encode C,
        SierpinskiGasketTasteGate_single_carrier_alignment_decode_encode P,
        SierpinskiGasketTasteGate_single_carrier_alignment_decode_encode N]

private theorem SierpinskiGasketTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SierpinskiGasketUp} :
    sierpinskiGasketToEventFlow x = sierpinskiGasketToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sierpinskiGasketFromEventFlow (sierpinskiGasketToEventFlow x) =
        sierpinskiGasketFromEventFlow (sierpinskiGasketToEventFlow y) :=
    congrArg sierpinskiGasketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SierpinskiGasketTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SierpinskiGasketTasteGate_single_carrier_alignment_round_trip y)))

instance sierpinskiGasketBHistCarrier : BHistCarrier SierpinskiGasketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sierpinskiGasketToEventFlow
  fromEventFlow := sierpinskiGasketFromEventFlow

instance sierpinskiGasketChapterTasteGate : ChapterTasteGate SierpinskiGasketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sierpinskiGasketFromEventFlow (sierpinskiGasketToEventFlow x) = some x
    exact SierpinskiGasketTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SierpinskiGasketTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate SierpinskiGasketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sierpinskiGasketChapterTasteGate

theorem SierpinskiGasketTasteGate_single_carrier_alignment :
    (forall x : SierpinskiGasketUp,
      BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
      Nonempty (BHistCarrier SierpinskiGasketUp) ∧
        Nonempty (ChapterTasteGate SierpinskiGasketUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    change sierpinskiGasketFromEventFlow (sierpinskiGasketToEventFlow x) = some x
    exact SierpinskiGasketTasteGate_single_carrier_alignment_round_trip x
  · constructor
    · exact ⟨sierpinskiGasketBHistCarrier⟩
    · exact ⟨sierpinskiGasketChapterTasteGate⟩

end BEDC.Derived.SierpinskiGasketUp
