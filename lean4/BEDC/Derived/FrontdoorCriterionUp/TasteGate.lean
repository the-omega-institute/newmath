import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FrontdoorCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FrontdoorCriterionUp : Type where
  | mk (T M Y I B A H C P N : BHist) : FrontdoorCriterionUp
  deriving DecidableEq

def frontdoorCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: frontdoorCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: frontdoorCriterionEncodeBHist h

def frontdoorCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (frontdoorCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (frontdoorCriterionDecodeBHist tail)

private theorem FrontdoorCriterionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, frontdoorCriterionDecodeBHist (frontdoorCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def frontdoorCriterionFields : FrontdoorCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FrontdoorCriterionUp.mk T M Y I B A H C P N => [T, M, Y, I, B, A, H, C, P, N]

def frontdoorCriterionToEventFlow : FrontdoorCriterionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (frontdoorCriterionFields x).map frontdoorCriterionEncodeBHist

private def frontdoorCriterionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => frontdoorCriterionEventAtDefault index rest

def frontdoorCriterionFromEventFlow : EventFlow → Option FrontdoorCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (FrontdoorCriterionUp.mk
        (frontdoorCriterionDecodeBHist (frontdoorCriterionEventAtDefault 0 ef))
        (frontdoorCriterionDecodeBHist (frontdoorCriterionEventAtDefault 1 ef))
        (frontdoorCriterionDecodeBHist (frontdoorCriterionEventAtDefault 2 ef))
        (frontdoorCriterionDecodeBHist (frontdoorCriterionEventAtDefault 3 ef))
        (frontdoorCriterionDecodeBHist (frontdoorCriterionEventAtDefault 4 ef))
        (frontdoorCriterionDecodeBHist (frontdoorCriterionEventAtDefault 5 ef))
        (frontdoorCriterionDecodeBHist (frontdoorCriterionEventAtDefault 6 ef))
        (frontdoorCriterionDecodeBHist (frontdoorCriterionEventAtDefault 7 ef))
        (frontdoorCriterionDecodeBHist (frontdoorCriterionEventAtDefault 8 ef))
        (frontdoorCriterionDecodeBHist (frontdoorCriterionEventAtDefault 9 ef)))

private theorem FrontdoorCriterionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FrontdoorCriterionUp,
      frontdoorCriterionFromEventFlow (frontdoorCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T M Y I B A H C P N =>
      change
        some
          (FrontdoorCriterionUp.mk
            (frontdoorCriterionDecodeBHist (frontdoorCriterionEncodeBHist T))
            (frontdoorCriterionDecodeBHist (frontdoorCriterionEncodeBHist M))
            (frontdoorCriterionDecodeBHist (frontdoorCriterionEncodeBHist Y))
            (frontdoorCriterionDecodeBHist (frontdoorCriterionEncodeBHist I))
            (frontdoorCriterionDecodeBHist (frontdoorCriterionEncodeBHist B))
            (frontdoorCriterionDecodeBHist (frontdoorCriterionEncodeBHist A))
            (frontdoorCriterionDecodeBHist (frontdoorCriterionEncodeBHist H))
            (frontdoorCriterionDecodeBHist (frontdoorCriterionEncodeBHist C))
            (frontdoorCriterionDecodeBHist (frontdoorCriterionEncodeBHist P))
            (frontdoorCriterionDecodeBHist (frontdoorCriterionEncodeBHist N))) =
          some (FrontdoorCriterionUp.mk T M Y I B A H C P N)
      rw [FrontdoorCriterionTasteGate_single_carrier_alignment_decode T,
        FrontdoorCriterionTasteGate_single_carrier_alignment_decode M,
        FrontdoorCriterionTasteGate_single_carrier_alignment_decode Y,
        FrontdoorCriterionTasteGate_single_carrier_alignment_decode I,
        FrontdoorCriterionTasteGate_single_carrier_alignment_decode B,
        FrontdoorCriterionTasteGate_single_carrier_alignment_decode A,
        FrontdoorCriterionTasteGate_single_carrier_alignment_decode H,
        FrontdoorCriterionTasteGate_single_carrier_alignment_decode C,
        FrontdoorCriterionTasteGate_single_carrier_alignment_decode P,
        FrontdoorCriterionTasteGate_single_carrier_alignment_decode N]

private theorem FrontdoorCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FrontdoorCriterionUp} :
    frontdoorCriterionToEventFlow x = frontdoorCriterionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      frontdoorCriterionFromEventFlow (frontdoorCriterionToEventFlow x) =
        frontdoorCriterionFromEventFlow (frontdoorCriterionToEventFlow y) :=
    congrArg frontdoorCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FrontdoorCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FrontdoorCriterionTasteGate_single_carrier_alignment_round_trip y)))

instance frontdoorCriterionBHistCarrier : BHistCarrier FrontdoorCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := frontdoorCriterionToEventFlow
  fromEventFlow := frontdoorCriterionFromEventFlow

instance frontdoorCriterionChapterTasteGate : ChapterTasteGate FrontdoorCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change frontdoorCriterionFromEventFlow (frontdoorCriterionToEventFlow x) = some x
    exact FrontdoorCriterionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FrontdoorCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate FrontdoorCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  frontdoorCriterionChapterTasteGate

theorem FrontdoorCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist, frontdoorCriterionDecodeBHist (frontdoorCriterionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier FrontdoorCriterionUp) ∧
        Nonempty (ChapterTasteGate FrontdoorCriterionUp) ∧
          frontdoorCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨FrontdoorCriterionTasteGate_single_carrier_alignment_decode,
      ⟨frontdoorCriterionBHistCarrier⟩,
      ⟨frontdoorCriterionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.FrontdoorCriterionUp
