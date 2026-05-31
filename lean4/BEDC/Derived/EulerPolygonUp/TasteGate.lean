import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EulerPolygonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EulerPolygonUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (M A L V D Q R H C P N : BHist) : EulerPolygonUp
  deriving DecidableEq

def eulerPolygonEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: eulerPolygonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: eulerPolygonEncodeBHist h

def eulerPolygonDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (eulerPolygonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (eulerPolygonDecodeBHist tail)

private theorem EulerPolygonTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, eulerPolygonDecodeBHist (eulerPolygonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def eulerPolygonFields : EulerPolygonUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EulerPolygonUp.mk M A L V D Q R H C P N => [M, A, L, V, D, Q, R, H, C, P, N]

def eulerPolygonToEventFlow : EulerPolygonUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (eulerPolygonFields x).map eulerPolygonEncodeBHist

private def EulerPolygonTasteGate_single_carrier_alignment_eventAt :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => EulerPolygonTasteGate_single_carrier_alignment_eventAt index rest

def eulerPolygonFromEventFlow : EventFlow -> Option EulerPolygonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (EulerPolygonUp.mk
        (eulerPolygonDecodeBHist (EulerPolygonTasteGate_single_carrier_alignment_eventAt 0 ef))
        (eulerPolygonDecodeBHist (EulerPolygonTasteGate_single_carrier_alignment_eventAt 1 ef))
        (eulerPolygonDecodeBHist (EulerPolygonTasteGate_single_carrier_alignment_eventAt 2 ef))
        (eulerPolygonDecodeBHist (EulerPolygonTasteGate_single_carrier_alignment_eventAt 3 ef))
        (eulerPolygonDecodeBHist (EulerPolygonTasteGate_single_carrier_alignment_eventAt 4 ef))
        (eulerPolygonDecodeBHist (EulerPolygonTasteGate_single_carrier_alignment_eventAt 5 ef))
        (eulerPolygonDecodeBHist (EulerPolygonTasteGate_single_carrier_alignment_eventAt 6 ef))
        (eulerPolygonDecodeBHist (EulerPolygonTasteGate_single_carrier_alignment_eventAt 7 ef))
        (eulerPolygonDecodeBHist (EulerPolygonTasteGate_single_carrier_alignment_eventAt 8 ef))
        (eulerPolygonDecodeBHist (EulerPolygonTasteGate_single_carrier_alignment_eventAt 9 ef))
        (eulerPolygonDecodeBHist (EulerPolygonTasteGate_single_carrier_alignment_eventAt 10 ef)))

private theorem EulerPolygonTasteGate_single_carrier_alignment_round_trip :
    forall x : EulerPolygonUp,
      eulerPolygonFromEventFlow (eulerPolygonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M A L V D Q R H C P N =>
      change
        some
          (EulerPolygonUp.mk
            (eulerPolygonDecodeBHist (eulerPolygonEncodeBHist M))
            (eulerPolygonDecodeBHist (eulerPolygonEncodeBHist A))
            (eulerPolygonDecodeBHist (eulerPolygonEncodeBHist L))
            (eulerPolygonDecodeBHist (eulerPolygonEncodeBHist V))
            (eulerPolygonDecodeBHist (eulerPolygonEncodeBHist D))
            (eulerPolygonDecodeBHist (eulerPolygonEncodeBHist Q))
            (eulerPolygonDecodeBHist (eulerPolygonEncodeBHist R))
            (eulerPolygonDecodeBHist (eulerPolygonEncodeBHist H))
            (eulerPolygonDecodeBHist (eulerPolygonEncodeBHist C))
            (eulerPolygonDecodeBHist (eulerPolygonEncodeBHist P))
            (eulerPolygonDecodeBHist (eulerPolygonEncodeBHist N))) =
          some (EulerPolygonUp.mk M A L V D Q R H C P N)
      rw [EulerPolygonTasteGate_single_carrier_alignment_decode_encode M,
        EulerPolygonTasteGate_single_carrier_alignment_decode_encode A,
        EulerPolygonTasteGate_single_carrier_alignment_decode_encode L,
        EulerPolygonTasteGate_single_carrier_alignment_decode_encode V,
        EulerPolygonTasteGate_single_carrier_alignment_decode_encode D,
        EulerPolygonTasteGate_single_carrier_alignment_decode_encode Q,
        EulerPolygonTasteGate_single_carrier_alignment_decode_encode R,
        EulerPolygonTasteGate_single_carrier_alignment_decode_encode H,
        EulerPolygonTasteGate_single_carrier_alignment_decode_encode C,
        EulerPolygonTasteGate_single_carrier_alignment_decode_encode P,
        EulerPolygonTasteGate_single_carrier_alignment_decode_encode N]

private theorem EulerPolygonTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : EulerPolygonUp} :
    eulerPolygonToEventFlow x = eulerPolygonToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      eulerPolygonFromEventFlow (eulerPolygonToEventFlow x) =
        eulerPolygonFromEventFlow (eulerPolygonToEventFlow y) :=
    congrArg eulerPolygonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (EulerPolygonTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (EulerPolygonTasteGate_single_carrier_alignment_round_trip y)))

instance eulerPolygonBHistCarrier : BHistCarrier EulerPolygonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := eulerPolygonToEventFlow
  fromEventFlow := eulerPolygonFromEventFlow

instance eulerPolygonChapterTasteGate : ChapterTasteGate EulerPolygonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change eulerPolygonFromEventFlow (eulerPolygonToEventFlow x) = some x
    exact EulerPolygonTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (EulerPolygonTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate EulerPolygonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  eulerPolygonChapterTasteGate

theorem EulerPolygonTasteGate_single_carrier_alignment :
    (forall h : BHist, eulerPolygonDecodeBHist (eulerPolygonEncodeBHist h) = h) ∧
      (forall x : EulerPolygonUp,
        eulerPolygonFromEventFlow (eulerPolygonToEventFlow x) = some x) ∧
        (forall x y : EulerPolygonUp,
          eulerPolygonToEventFlow x = eulerPolygonToEventFlow y -> x = y) ∧
          eulerPolygonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨EulerPolygonTasteGate_single_carrier_alignment_decode_encode,
      EulerPolygonTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => EulerPolygonTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.EulerPolygonUp
