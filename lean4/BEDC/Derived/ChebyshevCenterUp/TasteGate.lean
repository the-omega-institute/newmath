import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ChebyshevCenterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ChebyshevCenterUp : Type where
  | mk (carrier : BHist) : ChebyshevCenterUp
  deriving DecidableEq

def chebyshevCenterEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: chebyshevCenterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: chebyshevCenterEncodeBHist h

def chebyshevCenterDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (chebyshevCenterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (chebyshevCenterDecodeBHist tail)

private theorem chebyshevCenterDecode_encode_bhist :
    ∀ h : BHist, chebyshevCenterDecodeBHist (chebyshevCenterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def chebyshevCenterToEventFlow : ChebyshevCenterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ChebyshevCenterUp.mk carrier => [chebyshevCenterEncodeBHist carrier]

private def chebyshevCenterEventAtDefault : EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | [] => []
  | event :: _rest => event

def chebyshevCenterFromEventFlow (ef : EventFlow) : Option ChebyshevCenterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ChebyshevCenterUp.mk
      (chebyshevCenterDecodeBHist (chebyshevCenterEventAtDefault ef)))

private theorem chebyshevCenter_round_trip :
    ∀ x : ChebyshevCenterUp,
      chebyshevCenterFromEventFlow (chebyshevCenterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk carrier =>
      change
        some
            (ChebyshevCenterUp.mk
              (chebyshevCenterDecodeBHist (chebyshevCenterEncodeBHist carrier))) =
          some (ChebyshevCenterUp.mk carrier)
      exact congrArg (fun row => some (ChebyshevCenterUp.mk row))
        (chebyshevCenterDecode_encode_bhist carrier)

private theorem chebyshevCenterToEventFlow_injective {x y : ChebyshevCenterUp} :
    chebyshevCenterToEventFlow x = chebyshevCenterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      chebyshevCenterFromEventFlow (chebyshevCenterToEventFlow x) =
        chebyshevCenterFromEventFlow (chebyshevCenterToEventFlow y) :=
    congrArg chebyshevCenterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (chebyshevCenter_round_trip x).symm
      (Eq.trans hread (chebyshevCenter_round_trip y)))

instance chebyshevCenterBHistCarrier : BHistCarrier ChebyshevCenterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := chebyshevCenterToEventFlow
  fromEventFlow := chebyshevCenterFromEventFlow

instance chebyshevCenterChapterTasteGate : ChapterTasteGate ChebyshevCenterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change chebyshevCenterFromEventFlow (chebyshevCenterToEventFlow x) = some x
    exact chebyshevCenter_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (chebyshevCenterToEventFlow_injective heq)

theorem ChebyshevCenterTasteGate_single_carrier_alignment :
    (∀ h : BHist, chebyshevCenterDecodeBHist (chebyshevCenterEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ChebyshevCenterUp) ∧
        Nonempty (ChapterTasteGate ChebyshevCenterUp) ∧
          chebyshevCenterEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  constructor
  · exact chebyshevCenterDecode_encode_bhist
  · constructor
    · exact ⟨chebyshevCenterBHistCarrier⟩
    · constructor
      · exact ⟨chebyshevCenterChapterTasteGate⟩
      · rfl

end BEDC.Derived.ChebyshevCenterUp
