import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegulatedFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegulatedFunctionUp : Type where
  | mk (D M A T S H C P N : BHist) : RegulatedFunctionUp
  deriving DecidableEq

def regulatedFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regulatedFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regulatedFunctionEncodeBHist h

def regulatedFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regulatedFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regulatedFunctionDecodeBHist tail)

private theorem RegulatedFunctionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, regulatedFunctionDecodeBHist (regulatedFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regulatedFunctionFields : RegulatedFunctionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegulatedFunctionUp.mk D M A T S H C P N => [D, M, A, T, S, H, C, P, N]

def regulatedFunctionToEventFlow : RegulatedFunctionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (regulatedFunctionFields x).map regulatedFunctionEncodeBHist

private def regulatedFunctionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regulatedFunctionEventAtDefault index rest

def regulatedFunctionFromEventFlow : EventFlow → Option RegulatedFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RegulatedFunctionUp.mk
        (regulatedFunctionDecodeBHist (regulatedFunctionEventAtDefault 0 ef))
        (regulatedFunctionDecodeBHist (regulatedFunctionEventAtDefault 1 ef))
        (regulatedFunctionDecodeBHist (regulatedFunctionEventAtDefault 2 ef))
        (regulatedFunctionDecodeBHist (regulatedFunctionEventAtDefault 3 ef))
        (regulatedFunctionDecodeBHist (regulatedFunctionEventAtDefault 4 ef))
        (regulatedFunctionDecodeBHist (regulatedFunctionEventAtDefault 5 ef))
        (regulatedFunctionDecodeBHist (regulatedFunctionEventAtDefault 6 ef))
        (regulatedFunctionDecodeBHist (regulatedFunctionEventAtDefault 7 ef))
        (regulatedFunctionDecodeBHist (regulatedFunctionEventAtDefault 8 ef)))

private theorem RegulatedFunctionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegulatedFunctionUp,
      regulatedFunctionFromEventFlow (regulatedFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D M A T S H C P N =>
      change
        some
          (RegulatedFunctionUp.mk
            (regulatedFunctionDecodeBHist (regulatedFunctionEncodeBHist D))
            (regulatedFunctionDecodeBHist (regulatedFunctionEncodeBHist M))
            (regulatedFunctionDecodeBHist (regulatedFunctionEncodeBHist A))
            (regulatedFunctionDecodeBHist (regulatedFunctionEncodeBHist T))
            (regulatedFunctionDecodeBHist (regulatedFunctionEncodeBHist S))
            (regulatedFunctionDecodeBHist (regulatedFunctionEncodeBHist H))
            (regulatedFunctionDecodeBHist (regulatedFunctionEncodeBHist C))
            (regulatedFunctionDecodeBHist (regulatedFunctionEncodeBHist P))
            (regulatedFunctionDecodeBHist (regulatedFunctionEncodeBHist N))) =
          some (RegulatedFunctionUp.mk D M A T S H C P N)
      rw [RegulatedFunctionTasteGate_single_carrier_alignment_decode D,
        RegulatedFunctionTasteGate_single_carrier_alignment_decode M,
        RegulatedFunctionTasteGate_single_carrier_alignment_decode A,
        RegulatedFunctionTasteGate_single_carrier_alignment_decode T,
        RegulatedFunctionTasteGate_single_carrier_alignment_decode S,
        RegulatedFunctionTasteGate_single_carrier_alignment_decode H,
        RegulatedFunctionTasteGate_single_carrier_alignment_decode C,
        RegulatedFunctionTasteGate_single_carrier_alignment_decode P,
        RegulatedFunctionTasteGate_single_carrier_alignment_decode N]

private theorem RegulatedFunctionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegulatedFunctionUp} :
    regulatedFunctionToEventFlow x = regulatedFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regulatedFunctionFromEventFlow (regulatedFunctionToEventFlow x) =
        regulatedFunctionFromEventFlow (regulatedFunctionToEventFlow y) :=
    congrArg regulatedFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegulatedFunctionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RegulatedFunctionTasteGate_single_carrier_alignment_round_trip y)))

instance regulatedFunctionBHistCarrier : BHistCarrier RegulatedFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regulatedFunctionToEventFlow
  fromEventFlow := regulatedFunctionFromEventFlow

instance regulatedFunctionChapterTasteGate : ChapterTasteGate RegulatedFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regulatedFunctionFromEventFlow (regulatedFunctionToEventFlow x) = some x
    exact RegulatedFunctionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegulatedFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegulatedFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regulatedFunctionChapterTasteGate

theorem RegulatedFunctionTasteGate_single_carrier_alignment :
    (∀ h : BHist, regulatedFunctionDecodeBHist (regulatedFunctionEncodeBHist h) = h) ∧
      (∀ x : RegulatedFunctionUp,
        regulatedFunctionFromEventFlow (regulatedFunctionToEventFlow x) = some x) ∧
        (∀ x y : RegulatedFunctionUp,
          regulatedFunctionToEventFlow x = regulatedFunctionToEventFlow y → x = y) ∧
          regulatedFunctionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegulatedFunctionTasteGate_single_carrier_alignment_decode,
      RegulatedFunctionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => RegulatedFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegulatedFunctionUp
