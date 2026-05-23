import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyEstimateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyEstimateUp : Type where
  | mk : (R W D L M S H C P N : BHist) -> CauchyEstimateUp

def cauchyEstimateEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyEstimateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyEstimateEncodeBHist h

def cauchyEstimateDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyEstimateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyEstimateDecodeBHist tail)

theorem CauchyEstimateTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, cauchyEstimateDecodeBHist (cauchyEstimateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyEstimateFields : CauchyEstimateUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyEstimateUp.mk R W D L M S H C P N => [R, W, D, L, M, S, H, C, P, N]

def cauchyEstimateToEventFlow : CauchyEstimateUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyEstimateFields x).map cauchyEstimateEncodeBHist

def cauchyEstimateEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyEstimateEventAtDefault index rest

def cauchyEstimateFromEventFlow : EventFlow -> Option CauchyEstimateUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (CauchyEstimateUp.mk
          (cauchyEstimateDecodeBHist (cauchyEstimateEventAtDefault 0 ef))
          (cauchyEstimateDecodeBHist (cauchyEstimateEventAtDefault 1 ef))
          (cauchyEstimateDecodeBHist (cauchyEstimateEventAtDefault 2 ef))
          (cauchyEstimateDecodeBHist (cauchyEstimateEventAtDefault 3 ef))
          (cauchyEstimateDecodeBHist (cauchyEstimateEventAtDefault 4 ef))
          (cauchyEstimateDecodeBHist (cauchyEstimateEventAtDefault 5 ef))
          (cauchyEstimateDecodeBHist (cauchyEstimateEventAtDefault 6 ef))
          (cauchyEstimateDecodeBHist (cauchyEstimateEventAtDefault 7 ef))
          (cauchyEstimateDecodeBHist (cauchyEstimateEventAtDefault 8 ef))
          (cauchyEstimateDecodeBHist (cauchyEstimateEventAtDefault 9 ef)))

theorem CauchyEstimateTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyEstimateUp,
      cauchyEstimateFromEventFlow (cauchyEstimateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R W D L M S H C P N =>
      change
        some
          (CauchyEstimateUp.mk
            (cauchyEstimateDecodeBHist (cauchyEstimateEncodeBHist R))
            (cauchyEstimateDecodeBHist (cauchyEstimateEncodeBHist W))
            (cauchyEstimateDecodeBHist (cauchyEstimateEncodeBHist D))
            (cauchyEstimateDecodeBHist (cauchyEstimateEncodeBHist L))
            (cauchyEstimateDecodeBHist (cauchyEstimateEncodeBHist M))
            (cauchyEstimateDecodeBHist (cauchyEstimateEncodeBHist S))
            (cauchyEstimateDecodeBHist (cauchyEstimateEncodeBHist H))
            (cauchyEstimateDecodeBHist (cauchyEstimateEncodeBHist C))
            (cauchyEstimateDecodeBHist (cauchyEstimateEncodeBHist P))
            (cauchyEstimateDecodeBHist (cauchyEstimateEncodeBHist N))) =
          some (CauchyEstimateUp.mk R W D L M S H C P N)
      rw [CauchyEstimateTasteGate_single_carrier_alignment_decode R,
        CauchyEstimateTasteGate_single_carrier_alignment_decode W,
        CauchyEstimateTasteGate_single_carrier_alignment_decode D,
        CauchyEstimateTasteGate_single_carrier_alignment_decode L,
        CauchyEstimateTasteGate_single_carrier_alignment_decode M,
        CauchyEstimateTasteGate_single_carrier_alignment_decode S,
        CauchyEstimateTasteGate_single_carrier_alignment_decode H,
        CauchyEstimateTasteGate_single_carrier_alignment_decode C,
        CauchyEstimateTasteGate_single_carrier_alignment_decode P,
        CauchyEstimateTasteGate_single_carrier_alignment_decode N]

theorem CauchyEstimateTasteGate_single_carrier_alignment_injective {x y : CauchyEstimateUp} :
    cauchyEstimateToEventFlow x = cauchyEstimateToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyEstimateFromEventFlow (cauchyEstimateToEventFlow x) =
        cauchyEstimateFromEventFlow (cauchyEstimateToEventFlow y) :=
    congrArg cauchyEstimateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyEstimateTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyEstimateTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyEstimateBHistCarrier : BHistCarrier CauchyEstimateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyEstimateToEventFlow
  fromEventFlow := cauchyEstimateFromEventFlow

instance cauchyEstimateChapterTasteGate : ChapterTasteGate CauchyEstimateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x => CauchyEstimateTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyEstimateTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate CauchyEstimateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyEstimateChapterTasteGate

theorem CauchyEstimateTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyEstimateDecodeBHist (cauchyEstimateEncodeBHist h) = h) ∧
      (∀ x : CauchyEstimateUp,
        cauchyEstimateFromEventFlow (cauchyEstimateToEventFlow x) = some x) ∧
        (∀ x y : CauchyEstimateUp,
          cauchyEstimateToEventFlow x = cauchyEstimateToEventFlow y -> x = y) ∧
          cauchyEstimateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CauchyEstimateTasteGate_single_carrier_alignment_decode
  · constructor
    · exact CauchyEstimateTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact CauchyEstimateTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.CauchyEstimateUp
