import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTailGaugeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTailGaugeUp : Type where
  | mk (W R D G E H C P N : BHist) : RegularCauchyTailGaugeUp
  deriving DecidableEq

def regularCauchyTailGaugeEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTailGaugeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTailGaugeEncodeBHist h

def regularCauchyTailGaugeDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTailGaugeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTailGaugeDecodeBHist tail)

private theorem RegularCauchyTailGaugeTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      regularCauchyTailGaugeDecodeBHist (regularCauchyTailGaugeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyTailGaugeFields : RegularCauchyTailGaugeUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTailGaugeUp.mk W R D G E H C P N => [W, R, D, G, E, H, C, P, N]

def regularCauchyTailGaugeToEventFlow : RegularCauchyTailGaugeUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (regularCauchyTailGaugeFields x).map regularCauchyTailGaugeEncodeBHist

private def regularCauchyTailGaugeRawAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => regularCauchyTailGaugeRawAt n rest

private def regularCauchyTailGaugeLengthEq : Nat -> EventFlow -> Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => regularCauchyTailGaugeLengthEq n rest

def regularCauchyTailGaugeFromEventFlow
    (flow : EventFlow) : Option RegularCauchyTailGaugeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match regularCauchyTailGaugeLengthEq 9 flow with
  | true =>
      some
        (RegularCauchyTailGaugeUp.mk
          (regularCauchyTailGaugeDecodeBHist (regularCauchyTailGaugeRawAt 0 flow))
          (regularCauchyTailGaugeDecodeBHist (regularCauchyTailGaugeRawAt 1 flow))
          (regularCauchyTailGaugeDecodeBHist (regularCauchyTailGaugeRawAt 2 flow))
          (regularCauchyTailGaugeDecodeBHist (regularCauchyTailGaugeRawAt 3 flow))
          (regularCauchyTailGaugeDecodeBHist (regularCauchyTailGaugeRawAt 4 flow))
          (regularCauchyTailGaugeDecodeBHist (regularCauchyTailGaugeRawAt 5 flow))
          (regularCauchyTailGaugeDecodeBHist (regularCauchyTailGaugeRawAt 6 flow))
          (regularCauchyTailGaugeDecodeBHist (regularCauchyTailGaugeRawAt 7 flow))
          (regularCauchyTailGaugeDecodeBHist (regularCauchyTailGaugeRawAt 8 flow)))
  | false => none

private theorem regularCauchyTailGauge_round_trip :
    forall x : RegularCauchyTailGaugeUp,
      regularCauchyTailGaugeFromEventFlow (regularCauchyTailGaugeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W R D G E H C P N =>
      change
        some
          (RegularCauchyTailGaugeUp.mk
            (regularCauchyTailGaugeDecodeBHist (regularCauchyTailGaugeEncodeBHist W))
            (regularCauchyTailGaugeDecodeBHist (regularCauchyTailGaugeEncodeBHist R))
            (regularCauchyTailGaugeDecodeBHist (regularCauchyTailGaugeEncodeBHist D))
            (regularCauchyTailGaugeDecodeBHist (regularCauchyTailGaugeEncodeBHist G))
            (regularCauchyTailGaugeDecodeBHist (regularCauchyTailGaugeEncodeBHist E))
            (regularCauchyTailGaugeDecodeBHist (regularCauchyTailGaugeEncodeBHist H))
            (regularCauchyTailGaugeDecodeBHist (regularCauchyTailGaugeEncodeBHist C))
            (regularCauchyTailGaugeDecodeBHist (regularCauchyTailGaugeEncodeBHist P))
            (regularCauchyTailGaugeDecodeBHist (regularCauchyTailGaugeEncodeBHist N))) =
          some (RegularCauchyTailGaugeUp.mk W R D G E H C P N)
      rw [RegularCauchyTailGaugeTasteGate_single_carrier_alignment_decode W,
        RegularCauchyTailGaugeTasteGate_single_carrier_alignment_decode R,
        RegularCauchyTailGaugeTasteGate_single_carrier_alignment_decode D,
        RegularCauchyTailGaugeTasteGate_single_carrier_alignment_decode G,
        RegularCauchyTailGaugeTasteGate_single_carrier_alignment_decode E,
        RegularCauchyTailGaugeTasteGate_single_carrier_alignment_decode H,
        RegularCauchyTailGaugeTasteGate_single_carrier_alignment_decode C,
        RegularCauchyTailGaugeTasteGate_single_carrier_alignment_decode P,
        RegularCauchyTailGaugeTasteGate_single_carrier_alignment_decode N]

private theorem regularCauchyTailGaugeToEventFlow_injective
    {x y : RegularCauchyTailGaugeUp} :
    regularCauchyTailGaugeToEventFlow x = regularCauchyTailGaugeToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTailGaugeFromEventFlow (regularCauchyTailGaugeToEventFlow x) =
        regularCauchyTailGaugeFromEventFlow (regularCauchyTailGaugeToEventFlow y) :=
    congrArg regularCauchyTailGaugeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyTailGauge_round_trip x).symm
      (Eq.trans hread (regularCauchyTailGauge_round_trip y)))

instance regularCauchyTailGaugeBHistCarrier : BHistCarrier RegularCauchyTailGaugeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTailGaugeToEventFlow
  fromEventFlow := regularCauchyTailGaugeFromEventFlow

instance regularCauchyTailGaugeChapterTasteGate :
    ChapterTasteGate RegularCauchyTailGaugeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyTailGaugeFromEventFlow (regularCauchyTailGaugeToEventFlow x) = some x
    exact regularCauchyTailGauge_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyTailGaugeToEventFlow_injective heq)

theorem RegularCauchyTailGaugeTasteGate_single_carrier_alignment :
    (forall h : BHist, regularCauchyTailGaugeDecodeBHist
      (regularCauchyTailGaugeEncodeBHist h) = h) ∧
    (forall x : RegularCauchyTailGaugeUp,
      regularCauchyTailGaugeFromEventFlow (regularCauchyTailGaugeToEventFlow x) = some x) ∧
    (forall x y : RegularCauchyTailGaugeUp,
      regularCauchyTailGaugeToEventFlow x = regularCauchyTailGaugeToEventFlow y -> x = y) ∧
    regularCauchyTailGaugeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RegularCauchyTailGaugeTasteGate_single_carrier_alignment_decode
  · constructor
    · exact regularCauchyTailGauge_round_trip
    · constructor
      · intro x y heq
        exact regularCauchyTailGaugeToEventFlow_injective heq
      · rfl

end BEDC.Derived.RegularCauchyTailGaugeUp
