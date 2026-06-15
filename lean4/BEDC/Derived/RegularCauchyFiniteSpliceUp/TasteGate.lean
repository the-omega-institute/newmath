import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyFiniteSpliceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyFiniteSpliceUp : Type where
  | mk (k X Y W D R H C P N : BHist) : RegularCauchyFiniteSpliceUp
  deriving DecidableEq

def regularCauchyFiniteSpliceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyFiniteSpliceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyFiniteSpliceEncodeBHist h

def regularCauchyFiniteSpliceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyFiniteSpliceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyFiniteSpliceDecodeBHist tail)

private theorem RegularCauchyFiniteSpliceTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      regularCauchyFiniteSpliceDecodeBHist (regularCauchyFiniteSpliceEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyFiniteSpliceFields : RegularCauchyFiniteSpliceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyFiniteSpliceUp.mk k X Y W D R H C P N =>
      [k, X, Y, W, D, R, H, C, P, N]

def regularCauchyFiniteSpliceToEventFlow : RegularCauchyFiniteSpliceUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (regularCauchyFiniteSpliceFields x).map regularCauchyFiniteSpliceEncodeBHist

private def regularCauchyFiniteSpliceEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyFiniteSpliceEventAtDefault index rest

def regularCauchyFiniteSpliceFromEventFlow
    (ef : EventFlow) : Option RegularCauchyFiniteSpliceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyFiniteSpliceUp.mk
      (regularCauchyFiniteSpliceDecodeBHist (regularCauchyFiniteSpliceEventAtDefault 0 ef))
      (regularCauchyFiniteSpliceDecodeBHist (regularCauchyFiniteSpliceEventAtDefault 1 ef))
      (regularCauchyFiniteSpliceDecodeBHist (regularCauchyFiniteSpliceEventAtDefault 2 ef))
      (regularCauchyFiniteSpliceDecodeBHist (regularCauchyFiniteSpliceEventAtDefault 3 ef))
      (regularCauchyFiniteSpliceDecodeBHist (regularCauchyFiniteSpliceEventAtDefault 4 ef))
      (regularCauchyFiniteSpliceDecodeBHist (regularCauchyFiniteSpliceEventAtDefault 5 ef))
      (regularCauchyFiniteSpliceDecodeBHist (regularCauchyFiniteSpliceEventAtDefault 6 ef))
      (regularCauchyFiniteSpliceDecodeBHist (regularCauchyFiniteSpliceEventAtDefault 7 ef))
      (regularCauchyFiniteSpliceDecodeBHist (regularCauchyFiniteSpliceEventAtDefault 8 ef))
      (regularCauchyFiniteSpliceDecodeBHist (regularCauchyFiniteSpliceEventAtDefault 9 ef)))

private theorem RegularCauchyFiniteSpliceTasteGate_single_carrier_alignment_round_trip :
    forall x : RegularCauchyFiniteSpliceUp,
      regularCauchyFiniteSpliceFromEventFlow (regularCauchyFiniteSpliceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk k X Y W D R H C P N =>
      change
        some
          (RegularCauchyFiniteSpliceUp.mk
            (regularCauchyFiniteSpliceDecodeBHist (regularCauchyFiniteSpliceEncodeBHist k))
            (regularCauchyFiniteSpliceDecodeBHist (regularCauchyFiniteSpliceEncodeBHist X))
            (regularCauchyFiniteSpliceDecodeBHist (regularCauchyFiniteSpliceEncodeBHist Y))
            (regularCauchyFiniteSpliceDecodeBHist (regularCauchyFiniteSpliceEncodeBHist W))
            (regularCauchyFiniteSpliceDecodeBHist (regularCauchyFiniteSpliceEncodeBHist D))
            (regularCauchyFiniteSpliceDecodeBHist (regularCauchyFiniteSpliceEncodeBHist R))
            (regularCauchyFiniteSpliceDecodeBHist (regularCauchyFiniteSpliceEncodeBHist H))
            (regularCauchyFiniteSpliceDecodeBHist (regularCauchyFiniteSpliceEncodeBHist C))
            (regularCauchyFiniteSpliceDecodeBHist (regularCauchyFiniteSpliceEncodeBHist P))
            (regularCauchyFiniteSpliceDecodeBHist (regularCauchyFiniteSpliceEncodeBHist N))) =
          some (RegularCauchyFiniteSpliceUp.mk k X Y W D R H C P N)
      rw [RegularCauchyFiniteSpliceTasteGate_single_carrier_alignment_decode k,
        RegularCauchyFiniteSpliceTasteGate_single_carrier_alignment_decode X,
        RegularCauchyFiniteSpliceTasteGate_single_carrier_alignment_decode Y,
        RegularCauchyFiniteSpliceTasteGate_single_carrier_alignment_decode W,
        RegularCauchyFiniteSpliceTasteGate_single_carrier_alignment_decode D,
        RegularCauchyFiniteSpliceTasteGate_single_carrier_alignment_decode R,
        RegularCauchyFiniteSpliceTasteGate_single_carrier_alignment_decode H,
        RegularCauchyFiniteSpliceTasteGate_single_carrier_alignment_decode C,
        RegularCauchyFiniteSpliceTasteGate_single_carrier_alignment_decode P,
        RegularCauchyFiniteSpliceTasteGate_single_carrier_alignment_decode N]

private theorem RegularCauchyFiniteSpliceTasteGate_single_carrier_alignment_injective
    {x y : RegularCauchyFiniteSpliceUp} :
    regularCauchyFiniteSpliceToEventFlow x = regularCauchyFiniteSpliceToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyFiniteSpliceFromEventFlow (regularCauchyFiniteSpliceToEventFlow x) =
        regularCauchyFiniteSpliceFromEventFlow (regularCauchyFiniteSpliceToEventFlow y) :=
    congrArg regularCauchyFiniteSpliceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyFiniteSpliceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyFiniteSpliceTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyFiniteSpliceBHistCarrier :
    BHistCarrier RegularCauchyFiniteSpliceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyFiniteSpliceToEventFlow
  fromEventFlow := regularCauchyFiniteSpliceFromEventFlow

instance regularCauchyFiniteSpliceChapterTasteGate :
    ChapterTasteGate RegularCauchyFiniteSpliceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyFiniteSpliceFromEventFlow
        (regularCauchyFiniteSpliceToEventFlow x) = some x
    exact RegularCauchyFiniteSpliceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyFiniteSpliceTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyFiniteSpliceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyFiniteSpliceChapterTasteGate

theorem RegularCauchyFiniteSpliceTasteGate_single_carrier_alignment :
    ChapterTasteGate RegularCauchyFiniteSpliceUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact regularCauchyFiniteSpliceChapterTasteGate

end BEDC.Derived.RegularCauchyFiniteSpliceUp
