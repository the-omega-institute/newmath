import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DistanceToCompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DistanceToCompactUp : Type where
  | mk (X K L F R E H C P N : BHist) : DistanceToCompactUp
  deriving DecidableEq

def distanceToCompactEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: distanceToCompactEncodeBHist h
  | BHist.e1 h => BMark.b1 :: distanceToCompactEncodeBHist h

def distanceToCompactDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (distanceToCompactDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (distanceToCompactDecodeBHist tail)

private theorem DistanceToCompactTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, distanceToCompactDecodeBHist (distanceToCompactEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def distanceToCompactFields : DistanceToCompactUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DistanceToCompactUp.mk X K L F R E H C P N => [X, K, L, F, R, E, H, C, P, N]

def distanceToCompactToEventFlow : DistanceToCompactUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (distanceToCompactFields x).map distanceToCompactEncodeBHist

private def distanceToCompactEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => distanceToCompactEventAtDefault index rest

def distanceToCompactFromEventFlow (ef : EventFlow) : Option DistanceToCompactUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DistanceToCompactUp.mk
      (distanceToCompactDecodeBHist (distanceToCompactEventAtDefault 0 ef))
      (distanceToCompactDecodeBHist (distanceToCompactEventAtDefault 1 ef))
      (distanceToCompactDecodeBHist (distanceToCompactEventAtDefault 2 ef))
      (distanceToCompactDecodeBHist (distanceToCompactEventAtDefault 3 ef))
      (distanceToCompactDecodeBHist (distanceToCompactEventAtDefault 4 ef))
      (distanceToCompactDecodeBHist (distanceToCompactEventAtDefault 5 ef))
      (distanceToCompactDecodeBHist (distanceToCompactEventAtDefault 6 ef))
      (distanceToCompactDecodeBHist (distanceToCompactEventAtDefault 7 ef))
      (distanceToCompactDecodeBHist (distanceToCompactEventAtDefault 8 ef))
      (distanceToCompactDecodeBHist (distanceToCompactEventAtDefault 9 ef)))

private theorem DistanceToCompactTasteGate_single_carrier_alignment_round_trip
    (x : DistanceToCompactUp) :
    distanceToCompactFromEventFlow (distanceToCompactToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X K L F R E H C P N =>
      change
        some
          (DistanceToCompactUp.mk
            (distanceToCompactDecodeBHist (distanceToCompactEncodeBHist X))
            (distanceToCompactDecodeBHist (distanceToCompactEncodeBHist K))
            (distanceToCompactDecodeBHist (distanceToCompactEncodeBHist L))
            (distanceToCompactDecodeBHist (distanceToCompactEncodeBHist F))
            (distanceToCompactDecodeBHist (distanceToCompactEncodeBHist R))
            (distanceToCompactDecodeBHist (distanceToCompactEncodeBHist E))
            (distanceToCompactDecodeBHist (distanceToCompactEncodeBHist H))
            (distanceToCompactDecodeBHist (distanceToCompactEncodeBHist C))
            (distanceToCompactDecodeBHist (distanceToCompactEncodeBHist P))
            (distanceToCompactDecodeBHist (distanceToCompactEncodeBHist N))) =
          some (DistanceToCompactUp.mk X K L F R E H C P N)
      rw [DistanceToCompactTasteGate_single_carrier_alignment_decode X,
        DistanceToCompactTasteGate_single_carrier_alignment_decode K,
        DistanceToCompactTasteGate_single_carrier_alignment_decode L,
        DistanceToCompactTasteGate_single_carrier_alignment_decode F,
        DistanceToCompactTasteGate_single_carrier_alignment_decode R,
        DistanceToCompactTasteGate_single_carrier_alignment_decode E,
        DistanceToCompactTasteGate_single_carrier_alignment_decode H,
        DistanceToCompactTasteGate_single_carrier_alignment_decode C,
        DistanceToCompactTasteGate_single_carrier_alignment_decode P,
        DistanceToCompactTasteGate_single_carrier_alignment_decode N]

private theorem DistanceToCompactTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DistanceToCompactUp} :
    distanceToCompactToEventFlow x = distanceToCompactToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      distanceToCompactFromEventFlow (distanceToCompactToEventFlow x) =
        distanceToCompactFromEventFlow (distanceToCompactToEventFlow y) :=
    congrArg distanceToCompactFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DistanceToCompactTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DistanceToCompactTasteGate_single_carrier_alignment_round_trip y)))

instance distanceToCompactBHistCarrier : BHistCarrier DistanceToCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := distanceToCompactToEventFlow
  fromEventFlow := distanceToCompactFromEventFlow

instance distanceToCompactChapterTasteGate : ChapterTasteGate DistanceToCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change distanceToCompactFromEventFlow (distanceToCompactToEventFlow x) = some x
    exact DistanceToCompactTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DistanceToCompactTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def distanceToCompactTasteGate : ChapterTasteGate DistanceToCompactUp :=
  -- BEDC touchpoint anchor: BHist BMark
  distanceToCompactChapterTasteGate

theorem DistanceToCompactTasteGate_single_carrier_alignment :
    distanceToCompactEncodeBHist BHist.Empty = [] ∧
      distanceToCompactEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
        distanceToCompactEncodeBHist (BHist.e1 BHist.Empty) = [BMark.b1] ∧
          (∀ h : BHist, distanceToCompactDecodeBHist (distanceToCompactEncodeBHist h) = h) ∧
            (∀ x : DistanceToCompactUp,
              distanceToCompactFromEventFlow (distanceToCompactToEventFlow x) = some x) ∧
              Function.Injective distanceToCompactToEventFlow := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨rfl, rfl, rfl, DistanceToCompactTasteGate_single_carrier_alignment_decode,
      DistanceToCompactTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq => DistanceToCompactTasteGate_single_carrier_alignment_toEventFlow_injective heq⟩

end BEDC.Derived.DistanceToCompactUp
