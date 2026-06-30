import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AlmostPeriodicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AlmostPeriodicUp : Type where
  | mk (F T Nrel S M U H C P N : BHist) : AlmostPeriodicUp
  deriving DecidableEq

def almostPeriodicEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: almostPeriodicEncodeBHist h
  | BHist.e1 h => BMark.b1 :: almostPeriodicEncodeBHist h

def almostPeriodicDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (almostPeriodicDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (almostPeriodicDecodeBHist tail)

private theorem almostPeriodic_decode_encode_bhist :
    ∀ h : BHist, almostPeriodicDecodeBHist (almostPeriodicEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def almostPeriodicFields : AlmostPeriodicUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AlmostPeriodicUp.mk F T Nrel S M U H C P N => [F, T, Nrel, S, M, U, H, C, P, N]

def almostPeriodicToEventFlow : AlmostPeriodicUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (almostPeriodicFields x).map almostPeriodicEncodeBHist

private def almostPeriodicEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => almostPeriodicEventAtDefault index rest

def almostPeriodicFromEventFlow (ef : EventFlow) : Option AlmostPeriodicUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AlmostPeriodicUp.mk
      (almostPeriodicDecodeBHist (almostPeriodicEventAtDefault 0 ef))
      (almostPeriodicDecodeBHist (almostPeriodicEventAtDefault 1 ef))
      (almostPeriodicDecodeBHist (almostPeriodicEventAtDefault 2 ef))
      (almostPeriodicDecodeBHist (almostPeriodicEventAtDefault 3 ef))
      (almostPeriodicDecodeBHist (almostPeriodicEventAtDefault 4 ef))
      (almostPeriodicDecodeBHist (almostPeriodicEventAtDefault 5 ef))
      (almostPeriodicDecodeBHist (almostPeriodicEventAtDefault 6 ef))
      (almostPeriodicDecodeBHist (almostPeriodicEventAtDefault 7 ef))
      (almostPeriodicDecodeBHist (almostPeriodicEventAtDefault 8 ef))
      (almostPeriodicDecodeBHist (almostPeriodicEventAtDefault 9 ef)))

private theorem almostPeriodic_round_trip :
    ∀ x : AlmostPeriodicUp,
      almostPeriodicFromEventFlow (almostPeriodicToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F T Nrel S M U H C P N =>
      change
        some
          (AlmostPeriodicUp.mk
            (almostPeriodicDecodeBHist (almostPeriodicEncodeBHist F))
            (almostPeriodicDecodeBHist (almostPeriodicEncodeBHist T))
            (almostPeriodicDecodeBHist (almostPeriodicEncodeBHist Nrel))
            (almostPeriodicDecodeBHist (almostPeriodicEncodeBHist S))
            (almostPeriodicDecodeBHist (almostPeriodicEncodeBHist M))
            (almostPeriodicDecodeBHist (almostPeriodicEncodeBHist U))
            (almostPeriodicDecodeBHist (almostPeriodicEncodeBHist H))
            (almostPeriodicDecodeBHist (almostPeriodicEncodeBHist C))
            (almostPeriodicDecodeBHist (almostPeriodicEncodeBHist P))
            (almostPeriodicDecodeBHist (almostPeriodicEncodeBHist N))) =
          some (AlmostPeriodicUp.mk F T Nrel S M U H C P N)
      rw [almostPeriodic_decode_encode_bhist F,
        almostPeriodic_decode_encode_bhist T,
        almostPeriodic_decode_encode_bhist Nrel,
        almostPeriodic_decode_encode_bhist S,
        almostPeriodic_decode_encode_bhist M,
        almostPeriodic_decode_encode_bhist U,
        almostPeriodic_decode_encode_bhist H,
        almostPeriodic_decode_encode_bhist C,
        almostPeriodic_decode_encode_bhist P,
        almostPeriodic_decode_encode_bhist N]

private theorem almostPeriodicToEventFlow_injective
    {x y : AlmostPeriodicUp} :
    almostPeriodicToEventFlow x = almostPeriodicToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      almostPeriodicFromEventFlow (almostPeriodicToEventFlow x) =
        almostPeriodicFromEventFlow (almostPeriodicToEventFlow y) :=
    congrArg almostPeriodicFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (almostPeriodic_round_trip x).symm
      (Eq.trans hread (almostPeriodic_round_trip y)))

instance almostPeriodicBHistCarrier : BHistCarrier AlmostPeriodicUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := almostPeriodicToEventFlow
  fromEventFlow := almostPeriodicFromEventFlow

instance almostPeriodicChapterTasteGate : ChapterTasteGate AlmostPeriodicUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change almostPeriodicFromEventFlow (almostPeriodicToEventFlow x) = some x
    exact almostPeriodic_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (almostPeriodicToEventFlow_injective heq)

theorem AlmostPeriodicTasteGate_single_carrier_alignment :
    (forall h : BHist, almostPeriodicDecodeBHist (almostPeriodicEncodeBHist h) = h) ∧
      (forall x : AlmostPeriodicUp,
        almostPeriodicFromEventFlow (almostPeriodicToEventFlow x) = some x) ∧
        almostPeriodicEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ⟨almostPeriodic_decode_encode_bhist, almostPeriodic_round_trip, rfl⟩

end BEDC.Derived.AlmostPeriodicUp
