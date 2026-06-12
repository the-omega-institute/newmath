import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealDecimalNormalFormUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealDecimalNormalFormUp : Type where
  | mk (D I Q Y R E H C P N : BHist) : RealDecimalNormalFormUp
  deriving DecidableEq

def realDecimalNormalFormEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realDecimalNormalFormEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realDecimalNormalFormEncodeBHist h

def realDecimalNormalFormDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realDecimalNormalFormDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realDecimalNormalFormDecodeBHist tail)

private theorem RealDecimalNormalFormTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, realDecimalNormalFormDecodeBHist (realDecimalNormalFormEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realDecimalNormalFormFields : RealDecimalNormalFormUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealDecimalNormalFormUp.mk D I Q Y R E H C P N => [D, I, Q, Y, R, E, H, C, P, N]

def realDecimalNormalFormToEventFlow : RealDecimalNormalFormUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realDecimalNormalFormFields x).map realDecimalNormalFormEncodeBHist

def realDecimalNormalFormFromEventFlow : EventFlow → Option RealDecimalNormalFormUp
  -- BEDC touchpoint anchor: BHist BMark
  | [D, I, Q, Y, R, E, H, C, P, N] =>
      some
        (RealDecimalNormalFormUp.mk
          (realDecimalNormalFormDecodeBHist D)
          (realDecimalNormalFormDecodeBHist I)
          (realDecimalNormalFormDecodeBHist Q)
          (realDecimalNormalFormDecodeBHist Y)
          (realDecimalNormalFormDecodeBHist R)
          (realDecimalNormalFormDecodeBHist E)
          (realDecimalNormalFormDecodeBHist H)
          (realDecimalNormalFormDecodeBHist C)
          (realDecimalNormalFormDecodeBHist P)
          (realDecimalNormalFormDecodeBHist N))
  | _ => none

private theorem RealDecimalNormalFormTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealDecimalNormalFormUp,
      realDecimalNormalFormFromEventFlow (realDecimalNormalFormToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D I Q Y R E H C P N =>
      change
        some
          (RealDecimalNormalFormUp.mk
            (realDecimalNormalFormDecodeBHist (realDecimalNormalFormEncodeBHist D))
            (realDecimalNormalFormDecodeBHist (realDecimalNormalFormEncodeBHist I))
            (realDecimalNormalFormDecodeBHist (realDecimalNormalFormEncodeBHist Q))
            (realDecimalNormalFormDecodeBHist (realDecimalNormalFormEncodeBHist Y))
            (realDecimalNormalFormDecodeBHist (realDecimalNormalFormEncodeBHist R))
            (realDecimalNormalFormDecodeBHist (realDecimalNormalFormEncodeBHist E))
            (realDecimalNormalFormDecodeBHist (realDecimalNormalFormEncodeBHist H))
            (realDecimalNormalFormDecodeBHist (realDecimalNormalFormEncodeBHist C))
            (realDecimalNormalFormDecodeBHist (realDecimalNormalFormEncodeBHist P))
            (realDecimalNormalFormDecodeBHist (realDecimalNormalFormEncodeBHist N))) =
          some (RealDecimalNormalFormUp.mk D I Q Y R E H C P N)
      rw [RealDecimalNormalFormTasteGate_single_carrier_alignment_decode_encode D,
        RealDecimalNormalFormTasteGate_single_carrier_alignment_decode_encode I,
        RealDecimalNormalFormTasteGate_single_carrier_alignment_decode_encode Q,
        RealDecimalNormalFormTasteGate_single_carrier_alignment_decode_encode Y,
        RealDecimalNormalFormTasteGate_single_carrier_alignment_decode_encode R,
        RealDecimalNormalFormTasteGate_single_carrier_alignment_decode_encode E,
        RealDecimalNormalFormTasteGate_single_carrier_alignment_decode_encode H,
        RealDecimalNormalFormTasteGate_single_carrier_alignment_decode_encode C,
        RealDecimalNormalFormTasteGate_single_carrier_alignment_decode_encode P,
        RealDecimalNormalFormTasteGate_single_carrier_alignment_decode_encode N]

private theorem RealDecimalNormalFormTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealDecimalNormalFormUp} :
    realDecimalNormalFormToEventFlow x = realDecimalNormalFormToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realDecimalNormalFormFromEventFlow (realDecimalNormalFormToEventFlow x) =
        realDecimalNormalFormFromEventFlow (realDecimalNormalFormToEventFlow y) :=
    congrArg realDecimalNormalFormFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealDecimalNormalFormTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealDecimalNormalFormTasteGate_single_carrier_alignment_round_trip y)))

instance realDecimalNormalFormBHistCarrier : BHistCarrier RealDecimalNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realDecimalNormalFormToEventFlow
  fromEventFlow := realDecimalNormalFormFromEventFlow

instance realDecimalNormalFormChapterTasteGate : ChapterTasteGate RealDecimalNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realDecimalNormalFormFromEventFlow (realDecimalNormalFormToEventFlow x) = some x
    exact RealDecimalNormalFormTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealDecimalNormalFormTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def RealDecimalNormalFormTasteGate_single_carrier_alignment :
    (∀ x : RealDecimalNormalFormUp,
      realDecimalNormalFormFromEventFlow (realDecimalNormalFormToEventFlow x) = some x) ∧
      (∀ x y : RealDecimalNormalFormUp, x ≠ y →
        realDecimalNormalFormToEventFlow x ≠ realDecimalNormalFormToEventFlow y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · intro x
    exact RealDecimalNormalFormTasteGate_single_carrier_alignment_round_trip x
  · intro x y hxy heq
    exact hxy (RealDecimalNormalFormTasteGate_single_carrier_alignment_toEventFlow_injective heq)

end BEDC.Derived.RealDecimalNormalFormUp
