import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NadlerFixedPointUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NadlerFixedPointUp : Type where
  | mk (X K F V D L O R H C P Q : BHist) : NadlerFixedPointUp
  deriving DecidableEq

def nadlerFixedPointEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nadlerFixedPointEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nadlerFixedPointEncodeBHist h

def nadlerFixedPointDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nadlerFixedPointDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nadlerFixedPointDecodeBHist tail)

private theorem nadlerFixedPoint_decode_encode :
    ∀ h : BHist, nadlerFixedPointDecodeBHist (nadlerFixedPointEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def nadlerFixedPointFields : NadlerFixedPointUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NadlerFixedPointUp.mk X K F V D L O R H C P Q =>
      [X, K, F, V, D, L, O, R, H, C, P, Q]

def nadlerFixedPointToEventFlow : NadlerFixedPointUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (nadlerFixedPointFields x).map nadlerFixedPointEncodeBHist

private def nadlerFixedPointEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => nadlerFixedPointEventAtDefault index rest

def nadlerFixedPointFromEventFlow (ef : EventFlow) : Option NadlerFixedPointUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (NadlerFixedPointUp.mk
      (nadlerFixedPointDecodeBHist (nadlerFixedPointEventAtDefault 0 ef))
      (nadlerFixedPointDecodeBHist (nadlerFixedPointEventAtDefault 1 ef))
      (nadlerFixedPointDecodeBHist (nadlerFixedPointEventAtDefault 2 ef))
      (nadlerFixedPointDecodeBHist (nadlerFixedPointEventAtDefault 3 ef))
      (nadlerFixedPointDecodeBHist (nadlerFixedPointEventAtDefault 4 ef))
      (nadlerFixedPointDecodeBHist (nadlerFixedPointEventAtDefault 5 ef))
      (nadlerFixedPointDecodeBHist (nadlerFixedPointEventAtDefault 6 ef))
      (nadlerFixedPointDecodeBHist (nadlerFixedPointEventAtDefault 7 ef))
      (nadlerFixedPointDecodeBHist (nadlerFixedPointEventAtDefault 8 ef))
      (nadlerFixedPointDecodeBHist (nadlerFixedPointEventAtDefault 9 ef))
      (nadlerFixedPointDecodeBHist (nadlerFixedPointEventAtDefault 10 ef))
      (nadlerFixedPointDecodeBHist (nadlerFixedPointEventAtDefault 11 ef)))

private theorem nadlerFixedPoint_round_trip :
    ∀ x : NadlerFixedPointUp,
      nadlerFixedPointFromEventFlow (nadlerFixedPointToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X K F V D L O R H C P Q =>
      change
        some
          (NadlerFixedPointUp.mk
            (nadlerFixedPointDecodeBHist (nadlerFixedPointEncodeBHist X))
            (nadlerFixedPointDecodeBHist (nadlerFixedPointEncodeBHist K))
            (nadlerFixedPointDecodeBHist (nadlerFixedPointEncodeBHist F))
            (nadlerFixedPointDecodeBHist (nadlerFixedPointEncodeBHist V))
            (nadlerFixedPointDecodeBHist (nadlerFixedPointEncodeBHist D))
            (nadlerFixedPointDecodeBHist (nadlerFixedPointEncodeBHist L))
            (nadlerFixedPointDecodeBHist (nadlerFixedPointEncodeBHist O))
            (nadlerFixedPointDecodeBHist (nadlerFixedPointEncodeBHist R))
            (nadlerFixedPointDecodeBHist (nadlerFixedPointEncodeBHist H))
            (nadlerFixedPointDecodeBHist (nadlerFixedPointEncodeBHist C))
            (nadlerFixedPointDecodeBHist (nadlerFixedPointEncodeBHist P))
            (nadlerFixedPointDecodeBHist (nadlerFixedPointEncodeBHist Q))) =
          some (NadlerFixedPointUp.mk X K F V D L O R H C P Q)
      rw [nadlerFixedPoint_decode_encode X,
        nadlerFixedPoint_decode_encode K,
        nadlerFixedPoint_decode_encode F,
        nadlerFixedPoint_decode_encode V,
        nadlerFixedPoint_decode_encode D,
        nadlerFixedPoint_decode_encode L,
        nadlerFixedPoint_decode_encode O,
        nadlerFixedPoint_decode_encode R,
        nadlerFixedPoint_decode_encode H,
        nadlerFixedPoint_decode_encode C,
        nadlerFixedPoint_decode_encode P,
        nadlerFixedPoint_decode_encode Q]

private theorem nadlerFixedPointToEventFlow_injective {x y : NadlerFixedPointUp} :
    nadlerFixedPointToEventFlow x = nadlerFixedPointToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      nadlerFixedPointFromEventFlow (nadlerFixedPointToEventFlow x) =
        nadlerFixedPointFromEventFlow (nadlerFixedPointToEventFlow y) :=
    congrArg nadlerFixedPointFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (nadlerFixedPoint_round_trip x).symm
      (Eq.trans hread (nadlerFixedPoint_round_trip y)))

instance nadlerFixedPointBHistCarrier : BHistCarrier NadlerFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nadlerFixedPointToEventFlow
  fromEventFlow := nadlerFixedPointFromEventFlow

instance nadlerFixedPointChapterTasteGate :
    ChapterTasteGate NadlerFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change nadlerFixedPointFromEventFlow (nadlerFixedPointToEventFlow x) = some x
    exact nadlerFixedPoint_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (nadlerFixedPointToEventFlow_injective heq)

theorem NadlerFixedPointTasteGate_single_carrier_alignment :
    (∀ h : BHist, nadlerFixedPointDecodeBHist (nadlerFixedPointEncodeBHist h) = h) ∧
      (∀ x : NadlerFixedPointUp,
        nadlerFixedPointFromEventFlow (nadlerFixedPointToEventFlow x) = some x) ∧
        (∀ x y : NadlerFixedPointUp,
          nadlerFixedPointToEventFlow x = nadlerFixedPointToEventFlow y → x = y) ∧
          nadlerFixedPointEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨nadlerFixedPoint_decode_encode,
      nadlerFixedPoint_round_trip,
      (fun _ _ h => nadlerFixedPointToEventFlow_injective h),
      rfl⟩

end BEDC.Derived.NadlerFixedPointUp.TasteGate
