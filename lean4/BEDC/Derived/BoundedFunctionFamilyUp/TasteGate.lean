import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedFunctionFamilyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedFunctionFamilyUp : Type where
  | mk (X Y I M B U H C P N : BHist) : BoundedFunctionFamilyUp
  deriving DecidableEq

def boundedFunctionFamilyEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedFunctionFamilyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedFunctionFamilyEncodeBHist h

def boundedFunctionFamilyDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedFunctionFamilyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedFunctionFamilyDecodeBHist tail)

private theorem BoundedFunctionFamilyUpTasteGate_single_carrier_alignment_decode :
    forall h : BHist, boundedFunctionFamilyDecodeBHist
      (boundedFunctionFamilyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundedFunctionFamilyToEventFlow : BoundedFunctionFamilyUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedFunctionFamilyUp.mk X Y I M B U H C P N =>
      [[BMark.b0],
        boundedFunctionFamilyEncodeBHist X,
        [BMark.b1, BMark.b0],
        boundedFunctionFamilyEncodeBHist Y,
        [BMark.b1, BMark.b1, BMark.b0],
        boundedFunctionFamilyEncodeBHist I,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedFunctionFamilyEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedFunctionFamilyEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedFunctionFamilyEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedFunctionFamilyEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        boundedFunctionFamilyEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        boundedFunctionFamilyEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        boundedFunctionFamilyEncodeBHist N]

private def boundedFunctionFamilyEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => boundedFunctionFamilyEventAtDefault index rest

def boundedFunctionFamilyFromEventFlow (ef : EventFlow) : Option BoundedFunctionFamilyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BoundedFunctionFamilyUp.mk
      (boundedFunctionFamilyDecodeBHist (boundedFunctionFamilyEventAtDefault 1 ef))
      (boundedFunctionFamilyDecodeBHist (boundedFunctionFamilyEventAtDefault 3 ef))
      (boundedFunctionFamilyDecodeBHist (boundedFunctionFamilyEventAtDefault 5 ef))
      (boundedFunctionFamilyDecodeBHist (boundedFunctionFamilyEventAtDefault 7 ef))
      (boundedFunctionFamilyDecodeBHist (boundedFunctionFamilyEventAtDefault 9 ef))
      (boundedFunctionFamilyDecodeBHist (boundedFunctionFamilyEventAtDefault 11 ef))
      (boundedFunctionFamilyDecodeBHist (boundedFunctionFamilyEventAtDefault 13 ef))
      (boundedFunctionFamilyDecodeBHist (boundedFunctionFamilyEventAtDefault 15 ef))
      (boundedFunctionFamilyDecodeBHist (boundedFunctionFamilyEventAtDefault 17 ef))
      (boundedFunctionFamilyDecodeBHist (boundedFunctionFamilyEventAtDefault 19 ef)))

theorem BoundedFunctionFamilyUpTasteGate_single_carrier_alignment :
    ∀ x : BoundedFunctionFamilyUp,
      boundedFunctionFamilyFromEventFlow (boundedFunctionFamilyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y I M B U H C P N =>
      change
        some
          (BoundedFunctionFamilyUp.mk
            (boundedFunctionFamilyDecodeBHist (boundedFunctionFamilyEncodeBHist X))
            (boundedFunctionFamilyDecodeBHist (boundedFunctionFamilyEncodeBHist Y))
            (boundedFunctionFamilyDecodeBHist (boundedFunctionFamilyEncodeBHist I))
            (boundedFunctionFamilyDecodeBHist (boundedFunctionFamilyEncodeBHist M))
            (boundedFunctionFamilyDecodeBHist (boundedFunctionFamilyEncodeBHist B))
            (boundedFunctionFamilyDecodeBHist (boundedFunctionFamilyEncodeBHist U))
            (boundedFunctionFamilyDecodeBHist (boundedFunctionFamilyEncodeBHist H))
            (boundedFunctionFamilyDecodeBHist (boundedFunctionFamilyEncodeBHist C))
            (boundedFunctionFamilyDecodeBHist (boundedFunctionFamilyEncodeBHist P))
            (boundedFunctionFamilyDecodeBHist (boundedFunctionFamilyEncodeBHist N))) =
          some (BoundedFunctionFamilyUp.mk X Y I M B U H C P N)
      rw [BoundedFunctionFamilyUpTasteGate_single_carrier_alignment_decode X,
        BoundedFunctionFamilyUpTasteGate_single_carrier_alignment_decode Y,
        BoundedFunctionFamilyUpTasteGate_single_carrier_alignment_decode I,
        BoundedFunctionFamilyUpTasteGate_single_carrier_alignment_decode M,
        BoundedFunctionFamilyUpTasteGate_single_carrier_alignment_decode B,
        BoundedFunctionFamilyUpTasteGate_single_carrier_alignment_decode U,
        BoundedFunctionFamilyUpTasteGate_single_carrier_alignment_decode H,
        BoundedFunctionFamilyUpTasteGate_single_carrier_alignment_decode C,
        BoundedFunctionFamilyUpTasteGate_single_carrier_alignment_decode P,
        BoundedFunctionFamilyUpTasteGate_single_carrier_alignment_decode N]

private theorem BoundedFunctionFamilyUpTasteGate_single_carrier_alignment_injective
    {x y : BoundedFunctionFamilyUp} :
    boundedFunctionFamilyToEventFlow x = boundedFunctionFamilyToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedFunctionFamilyFromEventFlow (boundedFunctionFamilyToEventFlow x) =
        boundedFunctionFamilyFromEventFlow (boundedFunctionFamilyToEventFlow y) :=
    congrArg boundedFunctionFamilyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BoundedFunctionFamilyUpTasteGate_single_carrier_alignment x).symm
      (Eq.trans hread (BoundedFunctionFamilyUpTasteGate_single_carrier_alignment y)))

instance boundedFunctionFamilyBHistCarrier : BHistCarrier BoundedFunctionFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedFunctionFamilyToEventFlow
  fromEventFlow := boundedFunctionFamilyFromEventFlow

instance boundedFunctionFamilyChapterTasteGate : ChapterTasteGate BoundedFunctionFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := BoundedFunctionFamilyUpTasteGate_single_carrier_alignment
  layer_separation := by
    intro _x _y hxy heq
    exact hxy (BoundedFunctionFamilyUpTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate BoundedFunctionFamilyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  boundedFunctionFamilyChapterTasteGate

end BEDC.Derived.BoundedFunctionFamilyUp
