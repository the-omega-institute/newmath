import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EulerPolygonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EulerPolygonUp : Type where
  | mk (M A L V D Q R H C P N : BHist) : EulerPolygonUp
  deriving DecidableEq

def eulerPolygonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: eulerPolygonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: eulerPolygonEncodeBHist h

def eulerPolygonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (eulerPolygonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (eulerPolygonDecodeBHist tail)

private theorem EulerPolygonUpTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, eulerPolygonDecodeBHist (eulerPolygonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def eulerPolygonFields : EulerPolygonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EulerPolygonUp.mk M A L V D Q R H C P N => [M, A, L, V, D, Q, R, H, C, P, N]

def eulerPolygonToEventFlow : EulerPolygonUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (eulerPolygonFields x).map eulerPolygonEncodeBHist

private def eulerPolygonEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => eulerPolygonEventAtDefault index rest

def eulerPolygonFromEventFlow (ef : EventFlow) : Option EulerPolygonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EulerPolygonUp.mk
      (eulerPolygonDecodeBHist (eulerPolygonEventAtDefault 0 ef))
      (eulerPolygonDecodeBHist (eulerPolygonEventAtDefault 1 ef))
      (eulerPolygonDecodeBHist (eulerPolygonEventAtDefault 2 ef))
      (eulerPolygonDecodeBHist (eulerPolygonEventAtDefault 3 ef))
      (eulerPolygonDecodeBHist (eulerPolygonEventAtDefault 4 ef))
      (eulerPolygonDecodeBHist (eulerPolygonEventAtDefault 5 ef))
      (eulerPolygonDecodeBHist (eulerPolygonEventAtDefault 6 ef))
      (eulerPolygonDecodeBHist (eulerPolygonEventAtDefault 7 ef))
      (eulerPolygonDecodeBHist (eulerPolygonEventAtDefault 8 ef))
      (eulerPolygonDecodeBHist (eulerPolygonEventAtDefault 9 ef))
      (eulerPolygonDecodeBHist (eulerPolygonEventAtDefault 10 ef)))

private theorem EulerPolygonUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : EulerPolygonUp, eulerPolygonFromEventFlow (eulerPolygonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
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
      rw [EulerPolygonUpTasteGate_single_carrier_alignment_decode M,
        EulerPolygonUpTasteGate_single_carrier_alignment_decode A,
        EulerPolygonUpTasteGate_single_carrier_alignment_decode L,
        EulerPolygonUpTasteGate_single_carrier_alignment_decode V,
        EulerPolygonUpTasteGate_single_carrier_alignment_decode D,
        EulerPolygonUpTasteGate_single_carrier_alignment_decode Q,
        EulerPolygonUpTasteGate_single_carrier_alignment_decode R,
        EulerPolygonUpTasteGate_single_carrier_alignment_decode H,
        EulerPolygonUpTasteGate_single_carrier_alignment_decode C,
        EulerPolygonUpTasteGate_single_carrier_alignment_decode P,
        EulerPolygonUpTasteGate_single_carrier_alignment_decode N]

private theorem EulerPolygonUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : EulerPolygonUp} :
    eulerPolygonToEventFlow x = eulerPolygonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      eulerPolygonFromEventFlow (eulerPolygonToEventFlow x) =
        eulerPolygonFromEventFlow (eulerPolygonToEventFlow y) :=
    congrArg eulerPolygonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (EulerPolygonUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (EulerPolygonUpTasteGate_single_carrier_alignment_round_trip y)))

instance eulerPolygonBHistCarrier : BHistCarrier EulerPolygonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := eulerPolygonToEventFlow
  fromEventFlow := eulerPolygonFromEventFlow

instance eulerPolygonChapterTasteGate : ChapterTasteGate EulerPolygonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change eulerPolygonFromEventFlow (eulerPolygonToEventFlow x) = some x
    exact EulerPolygonUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (EulerPolygonUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem EulerPolygonUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, eulerPolygonDecodeBHist (eulerPolygonEncodeBHist h) = h) ∧
      (∀ x : EulerPolygonUp, eulerPolygonFromEventFlow (eulerPolygonToEventFlow x) = some x) ∧
        (∀ x y : EulerPolygonUp, eulerPolygonToEventFlow x = eulerPolygonToEventFlow y → x = y) ∧
          eulerPolygonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨EulerPolygonUpTasteGate_single_carrier_alignment_decode,
      EulerPolygonUpTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => EulerPolygonUpTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.EulerPolygonUp
