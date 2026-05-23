import BEDC.Derived.RegularCauchyProductUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyProductUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyProductUp : Type where
  | mk
      (A B WA WB DA DB D E R H C P N : BHist) :
      RegularCauchyProductUp
  deriving DecidableEq

def regularCauchyProductEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyProductEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyProductEncodeBHist h

def regularCauchyProductDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyProductDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyProductDecodeBHist tail)

private theorem regularCauchyProduct_decode_encode :
    ∀ h : BHist,
      regularCauchyProductDecodeBHist (regularCauchyProductEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyProductFields : RegularCauchyProductUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyProductUp.mk A B WA WB DA DB D E R H C P N =>
      [A, B, WA, WB, DA, DB, D, E, R, H, C, P, N]

def regularCauchyProductToEventFlow : RegularCauchyProductUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyProductFields x).map regularCauchyProductEncodeBHist

private def regularCauchyProductEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyProductEventAt index rest

def regularCauchyProductFromEventFlow : EventFlow → Option RegularCauchyProductUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (RegularCauchyProductUp.mk
          (regularCauchyProductDecodeBHist (regularCauchyProductEventAt 0 ef))
          (regularCauchyProductDecodeBHist (regularCauchyProductEventAt 1 ef))
          (regularCauchyProductDecodeBHist (regularCauchyProductEventAt 2 ef))
          (regularCauchyProductDecodeBHist (regularCauchyProductEventAt 3 ef))
          (regularCauchyProductDecodeBHist (regularCauchyProductEventAt 4 ef))
          (regularCauchyProductDecodeBHist (regularCauchyProductEventAt 5 ef))
          (regularCauchyProductDecodeBHist (regularCauchyProductEventAt 6 ef))
          (regularCauchyProductDecodeBHist (regularCauchyProductEventAt 7 ef))
          (regularCauchyProductDecodeBHist (regularCauchyProductEventAt 8 ef))
          (regularCauchyProductDecodeBHist (regularCauchyProductEventAt 9 ef))
          (regularCauchyProductDecodeBHist (regularCauchyProductEventAt 10 ef))
          (regularCauchyProductDecodeBHist (regularCauchyProductEventAt 11 ef))
          (regularCauchyProductDecodeBHist (regularCauchyProductEventAt 12 ef)))

private theorem regularCauchyProduct_round_trip (x : RegularCauchyProductUp) :
    regularCauchyProductFromEventFlow (regularCauchyProductToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A B WA WB DA DB D E R H C P N =>
      change
        some
            (RegularCauchyProductUp.mk
              (regularCauchyProductDecodeBHist (regularCauchyProductEncodeBHist A))
              (regularCauchyProductDecodeBHist (regularCauchyProductEncodeBHist B))
              (regularCauchyProductDecodeBHist (regularCauchyProductEncodeBHist WA))
              (regularCauchyProductDecodeBHist (regularCauchyProductEncodeBHist WB))
              (regularCauchyProductDecodeBHist (regularCauchyProductEncodeBHist DA))
              (regularCauchyProductDecodeBHist (regularCauchyProductEncodeBHist DB))
              (regularCauchyProductDecodeBHist (regularCauchyProductEncodeBHist D))
              (regularCauchyProductDecodeBHist (regularCauchyProductEncodeBHist E))
              (regularCauchyProductDecodeBHist (regularCauchyProductEncodeBHist R))
              (regularCauchyProductDecodeBHist (regularCauchyProductEncodeBHist H))
              (regularCauchyProductDecodeBHist (regularCauchyProductEncodeBHist C))
              (regularCauchyProductDecodeBHist (regularCauchyProductEncodeBHist P))
              (regularCauchyProductDecodeBHist (regularCauchyProductEncodeBHist N))) =
          some (RegularCauchyProductUp.mk A B WA WB DA DB D E R H C P N)
      have hmk :
          RegularCauchyProductUp.mk
              (regularCauchyProductDecodeBHist (regularCauchyProductEncodeBHist A))
              (regularCauchyProductDecodeBHist (regularCauchyProductEncodeBHist B))
              (regularCauchyProductDecodeBHist (regularCauchyProductEncodeBHist WA))
              (regularCauchyProductDecodeBHist (regularCauchyProductEncodeBHist WB))
              (regularCauchyProductDecodeBHist (regularCauchyProductEncodeBHist DA))
              (regularCauchyProductDecodeBHist (regularCauchyProductEncodeBHist DB))
              (regularCauchyProductDecodeBHist (regularCauchyProductEncodeBHist D))
              (regularCauchyProductDecodeBHist (regularCauchyProductEncodeBHist E))
              (regularCauchyProductDecodeBHist (regularCauchyProductEncodeBHist R))
              (regularCauchyProductDecodeBHist (regularCauchyProductEncodeBHist H))
              (regularCauchyProductDecodeBHist (regularCauchyProductEncodeBHist C))
              (regularCauchyProductDecodeBHist (regularCauchyProductEncodeBHist P))
              (regularCauchyProductDecodeBHist (regularCauchyProductEncodeBHist N)) =
            RegularCauchyProductUp.mk A B WA WB DA DB D E R H C P N := by
        rw [regularCauchyProduct_decode_encode A, regularCauchyProduct_decode_encode B,
          regularCauchyProduct_decode_encode WA, regularCauchyProduct_decode_encode WB,
          regularCauchyProduct_decode_encode DA, regularCauchyProduct_decode_encode DB,
          regularCauchyProduct_decode_encode D, regularCauchyProduct_decode_encode E,
          regularCauchyProduct_decode_encode R, regularCauchyProduct_decode_encode H,
          regularCauchyProduct_decode_encode C, regularCauchyProduct_decode_encode P,
          regularCauchyProduct_decode_encode N]
      exact congrArg some hmk

private theorem regularCauchyProductToEventFlow_injective {x y : RegularCauchyProductUp} :
    regularCauchyProductToEventFlow x = regularCauchyProductToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyProductFromEventFlow (regularCauchyProductToEventFlow x) =
        regularCauchyProductFromEventFlow (regularCauchyProductToEventFlow y) :=
    congrArg regularCauchyProductFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyProduct_round_trip x).symm
      (Eq.trans hread (regularCauchyProduct_round_trip y)))

instance regularCauchyProductBHistCarrier : BHistCarrier RegularCauchyProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyProductToEventFlow
  fromEventFlow := regularCauchyProductFromEventFlow

instance regularCauchyProductChapterTasteGate : ChapterTasteGate RegularCauchyProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := regularCauchyProduct_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyProductToEventFlow_injective heq)

theorem RegularCauchyProductTasteGate_single_carrier_alignment :
    (∀ x : RegularCauchyProductUp,
      regularCauchyProductFromEventFlow (regularCauchyProductToEventFlow x) = some x) ∧
      (∀ x w m,
        List.Mem w (regularCauchyProductToEventFlow x) →
          List.Mem m w → m = BMark.b0 ∨ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyProduct_round_trip
  · intro x w m hw hm
    exact event_flow_conservativity (S := regularCauchyProductToEventFlow x) hw hm

end BEDC.Derived.RegularCauchyProductUp
