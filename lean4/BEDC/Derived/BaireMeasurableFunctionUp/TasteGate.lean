import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BaireMeasurableFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BaireMeasurableFunctionUp : Type where
  | mk (X Y B G R O H C P N : BHist) : BaireMeasurableFunctionUp
  deriving DecidableEq

def baireMeasurableFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: baireMeasurableFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: baireMeasurableFunctionEncodeBHist h

def baireMeasurableFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (baireMeasurableFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (baireMeasurableFunctionDecodeBHist tail)

private theorem BaireMeasurableFunctionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, baireMeasurableFunctionDecodeBHist
      (baireMeasurableFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def baireMeasurableFunctionFields : BaireMeasurableFunctionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BaireMeasurableFunctionUp.mk X Y B G R O H C P N => [X, Y, B, G, R, O, H, C, P, N]

def baireMeasurableFunctionToEventFlow : BaireMeasurableFunctionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (baireMeasurableFunctionFields x).map baireMeasurableFunctionEncodeBHist

private def baireMeasurableFunctionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => baireMeasurableFunctionEventAtDefault index rest

def baireMeasurableFunctionFromEventFlow
    (ef : EventFlow) : Option BaireMeasurableFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BaireMeasurableFunctionUp.mk
      (baireMeasurableFunctionDecodeBHist (baireMeasurableFunctionEventAtDefault 0 ef))
      (baireMeasurableFunctionDecodeBHist (baireMeasurableFunctionEventAtDefault 1 ef))
      (baireMeasurableFunctionDecodeBHist (baireMeasurableFunctionEventAtDefault 2 ef))
      (baireMeasurableFunctionDecodeBHist (baireMeasurableFunctionEventAtDefault 3 ef))
      (baireMeasurableFunctionDecodeBHist (baireMeasurableFunctionEventAtDefault 4 ef))
      (baireMeasurableFunctionDecodeBHist (baireMeasurableFunctionEventAtDefault 5 ef))
      (baireMeasurableFunctionDecodeBHist (baireMeasurableFunctionEventAtDefault 6 ef))
      (baireMeasurableFunctionDecodeBHist (baireMeasurableFunctionEventAtDefault 7 ef))
      (baireMeasurableFunctionDecodeBHist (baireMeasurableFunctionEventAtDefault 8 ef))
      (baireMeasurableFunctionDecodeBHist (baireMeasurableFunctionEventAtDefault 9 ef)))

private theorem BaireMeasurableFunctionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BaireMeasurableFunctionUp,
      baireMeasurableFunctionFromEventFlow (baireMeasurableFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y B G R O H C P N =>
      change
        some
          (BaireMeasurableFunctionUp.mk
            (baireMeasurableFunctionDecodeBHist (baireMeasurableFunctionEncodeBHist X))
            (baireMeasurableFunctionDecodeBHist (baireMeasurableFunctionEncodeBHist Y))
            (baireMeasurableFunctionDecodeBHist (baireMeasurableFunctionEncodeBHist B))
            (baireMeasurableFunctionDecodeBHist (baireMeasurableFunctionEncodeBHist G))
            (baireMeasurableFunctionDecodeBHist (baireMeasurableFunctionEncodeBHist R))
            (baireMeasurableFunctionDecodeBHist (baireMeasurableFunctionEncodeBHist O))
            (baireMeasurableFunctionDecodeBHist (baireMeasurableFunctionEncodeBHist H))
            (baireMeasurableFunctionDecodeBHist (baireMeasurableFunctionEncodeBHist C))
            (baireMeasurableFunctionDecodeBHist (baireMeasurableFunctionEncodeBHist P))
            (baireMeasurableFunctionDecodeBHist (baireMeasurableFunctionEncodeBHist N))) =
          some (BaireMeasurableFunctionUp.mk X Y B G R O H C P N)
      rw [BaireMeasurableFunctionTasteGate_single_carrier_alignment_decode X,
        BaireMeasurableFunctionTasteGate_single_carrier_alignment_decode Y,
        BaireMeasurableFunctionTasteGate_single_carrier_alignment_decode B,
        BaireMeasurableFunctionTasteGate_single_carrier_alignment_decode G,
        BaireMeasurableFunctionTasteGate_single_carrier_alignment_decode R,
        BaireMeasurableFunctionTasteGate_single_carrier_alignment_decode O,
        BaireMeasurableFunctionTasteGate_single_carrier_alignment_decode H,
        BaireMeasurableFunctionTasteGate_single_carrier_alignment_decode C,
        BaireMeasurableFunctionTasteGate_single_carrier_alignment_decode P,
        BaireMeasurableFunctionTasteGate_single_carrier_alignment_decode N]

private theorem BaireMeasurableFunctionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BaireMeasurableFunctionUp} :
    baireMeasurableFunctionToEventFlow x = baireMeasurableFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      baireMeasurableFunctionFromEventFlow (baireMeasurableFunctionToEventFlow x) =
        baireMeasurableFunctionFromEventFlow (baireMeasurableFunctionToEventFlow y) :=
    congrArg baireMeasurableFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BaireMeasurableFunctionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BaireMeasurableFunctionTasteGate_single_carrier_alignment_round_trip y)))

instance baireMeasurableFunctionBHistCarrier : BHistCarrier BaireMeasurableFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := baireMeasurableFunctionToEventFlow
  fromEventFlow := baireMeasurableFunctionFromEventFlow

instance baireMeasurableFunctionChapterTasteGate :
    ChapterTasteGate BaireMeasurableFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change baireMeasurableFunctionFromEventFlow
      (baireMeasurableFunctionToEventFlow x) = some x
    exact BaireMeasurableFunctionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BaireMeasurableFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate BaireMeasurableFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  baireMeasurableFunctionChapterTasteGate

theorem BaireMeasurableFunctionTasteGate_single_carrier_alignment :
    ChapterTasteGate BaireMeasurableFunctionUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact baireMeasurableFunctionChapterTasteGate

end BEDC.Derived.BaireMeasurableFunctionUp
