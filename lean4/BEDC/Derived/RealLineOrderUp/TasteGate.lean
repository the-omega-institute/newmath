import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealLineOrderUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealLineOrderUp : Type where
  | mk (D S R L A E H C P N : BHist) : RealLineOrderUp
  deriving DecidableEq

def realLineOrderEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realLineOrderEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realLineOrderEncodeBHist h

def realLineOrderDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realLineOrderDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realLineOrderDecodeBHist tail)

private theorem realLineOrderDecode_encode_bhist :
    forall h : BHist, realLineOrderDecodeBHist (realLineOrderEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem realLineOrder_mk_congr
    {D D' S S' R R' L L' A A' E E' H H' C C' P P' N N' : BHist}
    (hD : D' = D) (hS : S' = S) (hR : R' = R) (hL : L' = L)
    (hA : A' = A) (hE : E' = E) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    RealLineOrderUp.mk D' S' R' L' A' E' H' C' P' N' =
      RealLineOrderUp.mk D S R L A E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hD
  cases hS
  cases hR
  cases hL
  cases hA
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def realLineOrderToEventFlow : RealLineOrderUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealLineOrderUp.mk D S R L A E H C P N =>
      [[BMark.b1, BMark.b0],
        realLineOrderEncodeBHist D,
        realLineOrderEncodeBHist S,
        realLineOrderEncodeBHist R,
        realLineOrderEncodeBHist L,
        realLineOrderEncodeBHist A,
        realLineOrderEncodeBHist E,
        realLineOrderEncodeBHist H,
        realLineOrderEncodeBHist C,
        realLineOrderEncodeBHist P,
        realLineOrderEncodeBHist N]

private def realLineOrderEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realLineOrderEventAtDefault index rest

def realLineOrderFromEventFlow (ef : EventFlow) : Option RealLineOrderUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealLineOrderUp.mk
      (realLineOrderDecodeBHist (realLineOrderEventAtDefault 1 ef))
      (realLineOrderDecodeBHist (realLineOrderEventAtDefault 2 ef))
      (realLineOrderDecodeBHist (realLineOrderEventAtDefault 3 ef))
      (realLineOrderDecodeBHist (realLineOrderEventAtDefault 4 ef))
      (realLineOrderDecodeBHist (realLineOrderEventAtDefault 5 ef))
      (realLineOrderDecodeBHist (realLineOrderEventAtDefault 6 ef))
      (realLineOrderDecodeBHist (realLineOrderEventAtDefault 7 ef))
      (realLineOrderDecodeBHist (realLineOrderEventAtDefault 8 ef))
      (realLineOrderDecodeBHist (realLineOrderEventAtDefault 9 ef))
      (realLineOrderDecodeBHist (realLineOrderEventAtDefault 10 ef)))

private theorem realLineOrder_round_trip :
    forall x : RealLineOrderUp,
      realLineOrderFromEventFlow (realLineOrderToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R L A E H C P N =>
      change
        some
          (RealLineOrderUp.mk
            (realLineOrderDecodeBHist (realLineOrderEncodeBHist D))
            (realLineOrderDecodeBHist (realLineOrderEncodeBHist S))
            (realLineOrderDecodeBHist (realLineOrderEncodeBHist R))
            (realLineOrderDecodeBHist (realLineOrderEncodeBHist L))
            (realLineOrderDecodeBHist (realLineOrderEncodeBHist A))
            (realLineOrderDecodeBHist (realLineOrderEncodeBHist E))
            (realLineOrderDecodeBHist (realLineOrderEncodeBHist H))
            (realLineOrderDecodeBHist (realLineOrderEncodeBHist C))
            (realLineOrderDecodeBHist (realLineOrderEncodeBHist P))
            (realLineOrderDecodeBHist (realLineOrderEncodeBHist N))) =
          some (RealLineOrderUp.mk D S R L A E H C P N)
      exact
        congrArg some
          (realLineOrder_mk_congr
            (realLineOrderDecode_encode_bhist D)
            (realLineOrderDecode_encode_bhist S)
            (realLineOrderDecode_encode_bhist R)
            (realLineOrderDecode_encode_bhist L)
            (realLineOrderDecode_encode_bhist A)
            (realLineOrderDecode_encode_bhist E)
            (realLineOrderDecode_encode_bhist H)
            (realLineOrderDecode_encode_bhist C)
            (realLineOrderDecode_encode_bhist P)
            (realLineOrderDecode_encode_bhist N))

private theorem realLineOrderToEventFlow_injective {x y : RealLineOrderUp} :
    realLineOrderToEventFlow x = realLineOrderToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realLineOrderFromEventFlow (realLineOrderToEventFlow x) =
        realLineOrderFromEventFlow (realLineOrderToEventFlow y) :=
    congrArg realLineOrderFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realLineOrder_round_trip x).symm
      (Eq.trans hread (realLineOrder_round_trip y)))

instance realLineOrderBHistCarrier : BHistCarrier RealLineOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realLineOrderToEventFlow
  fromEventFlow := realLineOrderFromEventFlow

instance realLineOrderChapterTasteGate : ChapterTasteGate RealLineOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realLineOrderFromEventFlow (realLineOrderToEventFlow x) = some x
    exact realLineOrder_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realLineOrderToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealLineOrderUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realLineOrderChapterTasteGate

theorem RealLineOrderTasteGate_single_carrier_alignment :
    (forall h : BHist, realLineOrderDecodeBHist (realLineOrderEncodeBHist h) = h) ∧
      (forall x : RealLineOrderUp, realLineOrderFromEventFlow (realLineOrderToEventFlow x) =
        some x) ∧
        (forall x y : RealLineOrderUp, realLineOrderToEventFlow x = realLineOrderToEventFlow y ->
          x = y) ∧ realLineOrderEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨realLineOrderDecode_encode_bhist,
      realLineOrder_round_trip,
      (fun _ _ heq => realLineOrderToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealLineOrderUp
