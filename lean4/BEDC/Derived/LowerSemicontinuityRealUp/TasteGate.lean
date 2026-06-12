import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LowerSemicontinuityRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LowerSemicontinuityRealUp : Type where
  | mk (X T F W R E O H C P N : BHist) : LowerSemicontinuityRealUp

def lowerSemicontinuityRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lowerSemicontinuityRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lowerSemicontinuityRealEncodeBHist h

def lowerSemicontinuityRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lowerSemicontinuityRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lowerSemicontinuityRealDecodeBHist tail)

private theorem LowerSemicontinuityRealTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      lowerSemicontinuityRealDecodeBHist (lowerSemicontinuityRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def lowerSemicontinuityRealFields : LowerSemicontinuityRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LowerSemicontinuityRealUp.mk X T F W R E O H C P N => [X, T, F, W, R, E, O, H, C, P, N]

def lowerSemicontinuityRealToEventFlow : LowerSemicontinuityRealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (lowerSemicontinuityRealFields x).map lowerSemicontinuityRealEncodeBHist

private def lowerSemicontinuityRealEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => lowerSemicontinuityRealEventAtDefault index rest

def lowerSemicontinuityRealFromEventFlow
    (ef : EventFlow) : Option LowerSemicontinuityRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LowerSemicontinuityRealUp.mk
      (lowerSemicontinuityRealDecodeBHist (lowerSemicontinuityRealEventAtDefault 0 ef))
      (lowerSemicontinuityRealDecodeBHist (lowerSemicontinuityRealEventAtDefault 1 ef))
      (lowerSemicontinuityRealDecodeBHist (lowerSemicontinuityRealEventAtDefault 2 ef))
      (lowerSemicontinuityRealDecodeBHist (lowerSemicontinuityRealEventAtDefault 3 ef))
      (lowerSemicontinuityRealDecodeBHist (lowerSemicontinuityRealEventAtDefault 4 ef))
      (lowerSemicontinuityRealDecodeBHist (lowerSemicontinuityRealEventAtDefault 5 ef))
      (lowerSemicontinuityRealDecodeBHist (lowerSemicontinuityRealEventAtDefault 6 ef))
      (lowerSemicontinuityRealDecodeBHist (lowerSemicontinuityRealEventAtDefault 7 ef))
      (lowerSemicontinuityRealDecodeBHist (lowerSemicontinuityRealEventAtDefault 8 ef))
      (lowerSemicontinuityRealDecodeBHist (lowerSemicontinuityRealEventAtDefault 9 ef))
      (lowerSemicontinuityRealDecodeBHist (lowerSemicontinuityRealEventAtDefault 10 ef)))

private theorem LowerSemicontinuityRealTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LowerSemicontinuityRealUp,
      lowerSemicontinuityRealFromEventFlow (lowerSemicontinuityRealToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X T F W R E O H C P N =>
      change
        some
          (LowerSemicontinuityRealUp.mk
            (lowerSemicontinuityRealDecodeBHist (lowerSemicontinuityRealEncodeBHist X))
            (lowerSemicontinuityRealDecodeBHist (lowerSemicontinuityRealEncodeBHist T))
            (lowerSemicontinuityRealDecodeBHist (lowerSemicontinuityRealEncodeBHist F))
            (lowerSemicontinuityRealDecodeBHist (lowerSemicontinuityRealEncodeBHist W))
            (lowerSemicontinuityRealDecodeBHist (lowerSemicontinuityRealEncodeBHist R))
            (lowerSemicontinuityRealDecodeBHist (lowerSemicontinuityRealEncodeBHist E))
            (lowerSemicontinuityRealDecodeBHist (lowerSemicontinuityRealEncodeBHist O))
            (lowerSemicontinuityRealDecodeBHist (lowerSemicontinuityRealEncodeBHist H))
            (lowerSemicontinuityRealDecodeBHist (lowerSemicontinuityRealEncodeBHist C))
            (lowerSemicontinuityRealDecodeBHist (lowerSemicontinuityRealEncodeBHist P))
            (lowerSemicontinuityRealDecodeBHist (lowerSemicontinuityRealEncodeBHist N))) =
          some (LowerSemicontinuityRealUp.mk X T F W R E O H C P N)
      rw [LowerSemicontinuityRealTasteGate_single_carrier_alignment_decode X,
        LowerSemicontinuityRealTasteGate_single_carrier_alignment_decode T,
        LowerSemicontinuityRealTasteGate_single_carrier_alignment_decode F,
        LowerSemicontinuityRealTasteGate_single_carrier_alignment_decode W,
        LowerSemicontinuityRealTasteGate_single_carrier_alignment_decode R,
        LowerSemicontinuityRealTasteGate_single_carrier_alignment_decode E,
        LowerSemicontinuityRealTasteGate_single_carrier_alignment_decode O,
        LowerSemicontinuityRealTasteGate_single_carrier_alignment_decode H,
        LowerSemicontinuityRealTasteGate_single_carrier_alignment_decode C,
        LowerSemicontinuityRealTasteGate_single_carrier_alignment_decode P,
        LowerSemicontinuityRealTasteGate_single_carrier_alignment_decode N]

private theorem LowerSemicontinuityRealTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LowerSemicontinuityRealUp} :
    lowerSemicontinuityRealToEventFlow x = lowerSemicontinuityRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lowerSemicontinuityRealFromEventFlow (lowerSemicontinuityRealToEventFlow x) =
        lowerSemicontinuityRealFromEventFlow (lowerSemicontinuityRealToEventFlow y) :=
    congrArg lowerSemicontinuityRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LowerSemicontinuityRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LowerSemicontinuityRealTasteGate_single_carrier_alignment_round_trip y)))

instance lowerSemicontinuityRealBHistCarrier :
    BHistCarrier LowerSemicontinuityRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lowerSemicontinuityRealToEventFlow
  fromEventFlow := lowerSemicontinuityRealFromEventFlow

instance lowerSemicontinuityRealChapterTasteGate :
    ChapterTasteGate LowerSemicontinuityRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lowerSemicontinuityRealFromEventFlow
      (lowerSemicontinuityRealToEventFlow x) = some x
    exact LowerSemicontinuityRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LowerSemicontinuityRealTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate LowerSemicontinuityRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  lowerSemicontinuityRealChapterTasteGate

theorem LowerSemicontinuityRealTasteGate_single_carrier_alignment :
    (∃ carrier : BHistCarrier LowerSemicontinuityRealUp,
        Nonempty (@ChapterTasteGate LowerSemicontinuityRealUp carrier)) ∧
      (∀ h : BHist,
        lowerSemicontinuityRealDecodeBHist (lowerSemicontinuityRealEncodeBHist h) = h) ∧
        (∀ x : LowerSemicontinuityRealUp,
          lowerSemicontinuityRealFromEventFlow
            (lowerSemicontinuityRealToEventFlow x) = some x) ∧
          lowerSemicontinuityRealEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨⟨lowerSemicontinuityRealBHistCarrier,
        ⟨lowerSemicontinuityRealChapterTasteGate⟩⟩,
      LowerSemicontinuityRealTasteGate_single_carrier_alignment_decode,
      LowerSemicontinuityRealTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.LowerSemicontinuityRealUp
