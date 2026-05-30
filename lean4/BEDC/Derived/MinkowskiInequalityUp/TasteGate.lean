import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MinkowskiInequalityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MinkowskiInequalityUp : Type where
  | mk (X Y Z A B U V C D E F H T P N : BHist) : MinkowskiInequalityUp
  deriving DecidableEq

def minkowskiInequalityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: minkowskiInequalityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: minkowskiInequalityEncodeBHist h

def minkowskiInequalityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (minkowskiInequalityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (minkowskiInequalityDecodeBHist tail)

private theorem MinkowskiInequalityTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      minkowskiInequalityDecodeBHist (minkowskiInequalityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def minkowskiInequalityFields : MinkowskiInequalityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MinkowskiInequalityUp.mk X Y Z A B U V C D E F H T P N =>
      [X, Y, Z, A, B, U, V, C, D, E, F, H, T, P, N]

def minkowskiInequalityToEventFlow : MinkowskiInequalityUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (minkowskiInequalityFields x).map minkowskiInequalityEncodeBHist

private def minkowskiInequalityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => minkowskiInequalityEventAtDefault index rest

def minkowskiInequalityFromEventFlow (ef : EventFlow) : Option MinkowskiInequalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MinkowskiInequalityUp.mk
      (minkowskiInequalityDecodeBHist (minkowskiInequalityEventAtDefault 0 ef))
      (minkowskiInequalityDecodeBHist (minkowskiInequalityEventAtDefault 1 ef))
      (minkowskiInequalityDecodeBHist (minkowskiInequalityEventAtDefault 2 ef))
      (minkowskiInequalityDecodeBHist (minkowskiInequalityEventAtDefault 3 ef))
      (minkowskiInequalityDecodeBHist (minkowskiInequalityEventAtDefault 4 ef))
      (minkowskiInequalityDecodeBHist (minkowskiInequalityEventAtDefault 5 ef))
      (minkowskiInequalityDecodeBHist (minkowskiInequalityEventAtDefault 6 ef))
      (minkowskiInequalityDecodeBHist (minkowskiInequalityEventAtDefault 7 ef))
      (minkowskiInequalityDecodeBHist (minkowskiInequalityEventAtDefault 8 ef))
      (minkowskiInequalityDecodeBHist (minkowskiInequalityEventAtDefault 9 ef))
      (minkowskiInequalityDecodeBHist (minkowskiInequalityEventAtDefault 10 ef))
      (minkowskiInequalityDecodeBHist (minkowskiInequalityEventAtDefault 11 ef))
      (minkowskiInequalityDecodeBHist (minkowskiInequalityEventAtDefault 12 ef))
      (minkowskiInequalityDecodeBHist (minkowskiInequalityEventAtDefault 13 ef))
      (minkowskiInequalityDecodeBHist (minkowskiInequalityEventAtDefault 14 ef)))

private theorem MinkowskiInequalityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MinkowskiInequalityUp,
      minkowskiInequalityFromEventFlow (minkowskiInequalityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y Z A B U V C D E F H T P N =>
      change
        some
          (MinkowskiInequalityUp.mk
            (minkowskiInequalityDecodeBHist (minkowskiInequalityEncodeBHist X))
            (minkowskiInequalityDecodeBHist (minkowskiInequalityEncodeBHist Y))
            (minkowskiInequalityDecodeBHist (minkowskiInequalityEncodeBHist Z))
            (minkowskiInequalityDecodeBHist (minkowskiInequalityEncodeBHist A))
            (minkowskiInequalityDecodeBHist (minkowskiInequalityEncodeBHist B))
            (minkowskiInequalityDecodeBHist (minkowskiInequalityEncodeBHist U))
            (minkowskiInequalityDecodeBHist (minkowskiInequalityEncodeBHist V))
            (minkowskiInequalityDecodeBHist (minkowskiInequalityEncodeBHist C))
            (minkowskiInequalityDecodeBHist (minkowskiInequalityEncodeBHist D))
            (minkowskiInequalityDecodeBHist (minkowskiInequalityEncodeBHist E))
            (minkowskiInequalityDecodeBHist (minkowskiInequalityEncodeBHist F))
            (minkowskiInequalityDecodeBHist (minkowskiInequalityEncodeBHist H))
            (minkowskiInequalityDecodeBHist (minkowskiInequalityEncodeBHist T))
            (minkowskiInequalityDecodeBHist (minkowskiInequalityEncodeBHist P))
            (minkowskiInequalityDecodeBHist (minkowskiInequalityEncodeBHist N))) =
          some (MinkowskiInequalityUp.mk X Y Z A B U V C D E F H T P N)
      rw [MinkowskiInequalityTasteGate_single_carrier_alignment_decode X,
        MinkowskiInequalityTasteGate_single_carrier_alignment_decode Y,
        MinkowskiInequalityTasteGate_single_carrier_alignment_decode Z,
        MinkowskiInequalityTasteGate_single_carrier_alignment_decode A,
        MinkowskiInequalityTasteGate_single_carrier_alignment_decode B,
        MinkowskiInequalityTasteGate_single_carrier_alignment_decode U,
        MinkowskiInequalityTasteGate_single_carrier_alignment_decode V,
        MinkowskiInequalityTasteGate_single_carrier_alignment_decode C,
        MinkowskiInequalityTasteGate_single_carrier_alignment_decode D,
        MinkowskiInequalityTasteGate_single_carrier_alignment_decode E,
        MinkowskiInequalityTasteGate_single_carrier_alignment_decode F,
        MinkowskiInequalityTasteGate_single_carrier_alignment_decode H,
        MinkowskiInequalityTasteGate_single_carrier_alignment_decode T,
        MinkowskiInequalityTasteGate_single_carrier_alignment_decode P,
        MinkowskiInequalityTasteGate_single_carrier_alignment_decode N]

private theorem MinkowskiInequalityTasteGate_single_carrier_alignment_injective
    {x y : MinkowskiInequalityUp} :
    minkowskiInequalityToEventFlow x = minkowskiInequalityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      minkowskiInequalityFromEventFlow (minkowskiInequalityToEventFlow x) =
        minkowskiInequalityFromEventFlow (minkowskiInequalityToEventFlow y) :=
    congrArg minkowskiInequalityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MinkowskiInequalityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MinkowskiInequalityTasteGate_single_carrier_alignment_round_trip y)))

instance minkowskiInequalityBHistCarrier : BHistCarrier MinkowskiInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := minkowskiInequalityToEventFlow
  fromEventFlow := minkowskiInequalityFromEventFlow

instance minkowskiInequalityChapterTasteGate : ChapterTasteGate MinkowskiInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change minkowskiInequalityFromEventFlow (minkowskiInequalityToEventFlow x) = some x
    exact MinkowskiInequalityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MinkowskiInequalityTasteGate_single_carrier_alignment_injective heq)

theorem MinkowskiInequalityTasteGate_single_carrier_alignment :
    ChapterTasteGate MinkowskiInequalityUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact minkowskiInequalityChapterTasteGate

end BEDC.Derived.MinkowskiInequalityUp
