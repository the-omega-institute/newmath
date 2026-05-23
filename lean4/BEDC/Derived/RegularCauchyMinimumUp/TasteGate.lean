import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyMinimumUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyMinimumUp : Type where
  | mk (X Y T L D A B W H C P N : BHist) : RegularCauchyMinimumUp
  deriving DecidableEq

def regularCauchyMinimumEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyMinimumEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyMinimumEncodeBHist h

def regularCauchyMinimumDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyMinimumDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyMinimumDecodeBHist tail)

private theorem RegularCauchyMinimumTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, regularCauchyMinimumDecodeBHist (regularCauchyMinimumEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyMinimumToEventFlow : RegularCauchyMinimumUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyMinimumUp.mk X Y T L D A B W H C P N =>
      [[BMark.b0],
        regularCauchyMinimumEncodeBHist X,
        [BMark.b1, BMark.b0],
        regularCauchyMinimumEncodeBHist Y,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMinimumEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMinimumEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMinimumEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMinimumEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMinimumEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyMinimumEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyMinimumEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMinimumEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMinimumEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyMinimumEncodeBHist N]

private def regularCauchyMinimumEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyMinimumEventAtDefault index rest

def regularCauchyMinimumFromEventFlow (ef : EventFlow) : Option RegularCauchyMinimumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyMinimumUp.mk
      (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEventAtDefault 1 ef))
      (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEventAtDefault 3 ef))
      (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEventAtDefault 5 ef))
      (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEventAtDefault 7 ef))
      (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEventAtDefault 9 ef))
      (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEventAtDefault 11 ef))
      (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEventAtDefault 13 ef))
      (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEventAtDefault 15 ef))
      (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEventAtDefault 17 ef))
      (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEventAtDefault 19 ef))
      (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEventAtDefault 21 ef))
      (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEventAtDefault 23 ef)))

private theorem RegularCauchyMinimumTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyMinimumUp,
      regularCauchyMinimumFromEventFlow (regularCauchyMinimumToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y T L D A B W H C P N =>
      change
        some
          (RegularCauchyMinimumUp.mk
            (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEncodeBHist X))
            (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEncodeBHist Y))
            (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEncodeBHist T))
            (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEncodeBHist L))
            (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEncodeBHist D))
            (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEncodeBHist A))
            (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEncodeBHist B))
            (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEncodeBHist W))
            (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEncodeBHist H))
            (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEncodeBHist C))
            (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEncodeBHist P))
            (regularCauchyMinimumDecodeBHist (regularCauchyMinimumEncodeBHist N))) =
          some (RegularCauchyMinimumUp.mk X Y T L D A B W H C P N)
      rw [RegularCauchyMinimumTasteGate_single_carrier_alignment_decode X,
        RegularCauchyMinimumTasteGate_single_carrier_alignment_decode Y,
        RegularCauchyMinimumTasteGate_single_carrier_alignment_decode T,
        RegularCauchyMinimumTasteGate_single_carrier_alignment_decode L,
        RegularCauchyMinimumTasteGate_single_carrier_alignment_decode D,
        RegularCauchyMinimumTasteGate_single_carrier_alignment_decode A,
        RegularCauchyMinimumTasteGate_single_carrier_alignment_decode B,
        RegularCauchyMinimumTasteGate_single_carrier_alignment_decode W,
        RegularCauchyMinimumTasteGate_single_carrier_alignment_decode H,
        RegularCauchyMinimumTasteGate_single_carrier_alignment_decode C,
        RegularCauchyMinimumTasteGate_single_carrier_alignment_decode P,
        RegularCauchyMinimumTasteGate_single_carrier_alignment_decode N]

private theorem RegularCauchyMinimumTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyMinimumUp} :
    regularCauchyMinimumToEventFlow x = regularCauchyMinimumToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyMinimumFromEventFlow (regularCauchyMinimumToEventFlow x) =
        regularCauchyMinimumFromEventFlow (regularCauchyMinimumToEventFlow y) :=
    congrArg regularCauchyMinimumFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyMinimumTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RegularCauchyMinimumTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyMinimumBHistCarrier : BHistCarrier RegularCauchyMinimumUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyMinimumToEventFlow
  fromEventFlow := regularCauchyMinimumFromEventFlow

instance regularCauchyMinimumChapterTasteGate : ChapterTasteGate RegularCauchyMinimumUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyMinimumFromEventFlow (regularCauchyMinimumToEventFlow x) = some x
    exact RegularCauchyMinimumTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyMinimumTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RegularCauchyMinimumTasteGate_single_carrier_alignment :
    (forall h : BHist,
      regularCauchyMinimumDecodeBHist (regularCauchyMinimumEncodeBHist h) = h) /\
      (forall x : RegularCauchyMinimumUp,
        regularCauchyMinimumFromEventFlow (regularCauchyMinimumToEventFlow x) = some x) /\
      (forall x y : RegularCauchyMinimumUp,
        regularCauchyMinimumToEventFlow x = regularCauchyMinimumToEventFlow y -> x = y) /\
      regularCauchyMinimumEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RegularCauchyMinimumTasteGate_single_carrier_alignment_decode,
      RegularCauchyMinimumTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RegularCauchyMinimumTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyMinimumUp
