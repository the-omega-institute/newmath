import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FastCauchyNormalFormUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FastCauchyNormalFormUp : Type where
  | mk (D S R E C H Q P N : BHist) : FastCauchyNormalFormUp
  deriving DecidableEq

def fastCauchyNormalFormEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fastCauchyNormalFormEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fastCauchyNormalFormEncodeBHist h

def fastCauchyNormalFormDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fastCauchyNormalFormDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fastCauchyNormalFormDecodeBHist tail)

private theorem FastCauchyNormalFormTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      fastCauchyNormalFormDecodeBHist (fastCauchyNormalFormEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def fastCauchyNormalFormFields : FastCauchyNormalFormUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FastCauchyNormalFormUp.mk D S R E C H Q P N => [D, S, R, E, C, H, Q, P, N]

def fastCauchyNormalFormToEventFlow : FastCauchyNormalFormUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (fastCauchyNormalFormFields x).map fastCauchyNormalFormEncodeBHist

private def fastCauchyNormalFormEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => fastCauchyNormalFormEventAt index rest

def fastCauchyNormalFormFromEventFlow (flow : EventFlow) : Option FastCauchyNormalFormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FastCauchyNormalFormUp.mk
      (fastCauchyNormalFormDecodeBHist (fastCauchyNormalFormEventAt 0 flow))
      (fastCauchyNormalFormDecodeBHist (fastCauchyNormalFormEventAt 1 flow))
      (fastCauchyNormalFormDecodeBHist (fastCauchyNormalFormEventAt 2 flow))
      (fastCauchyNormalFormDecodeBHist (fastCauchyNormalFormEventAt 3 flow))
      (fastCauchyNormalFormDecodeBHist (fastCauchyNormalFormEventAt 4 flow))
      (fastCauchyNormalFormDecodeBHist (fastCauchyNormalFormEventAt 5 flow))
      (fastCauchyNormalFormDecodeBHist (fastCauchyNormalFormEventAt 6 flow))
      (fastCauchyNormalFormDecodeBHist (fastCauchyNormalFormEventAt 7 flow))
      (fastCauchyNormalFormDecodeBHist (fastCauchyNormalFormEventAt 8 flow)))

private theorem FastCauchyNormalFormTasteGate_single_carrier_alignment_round_trip
    (x : FastCauchyNormalFormUp) :
    fastCauchyNormalFormFromEventFlow (fastCauchyNormalFormToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D S R E C H Q P N =>
      change
        some
          (FastCauchyNormalFormUp.mk
            (fastCauchyNormalFormDecodeBHist (fastCauchyNormalFormEncodeBHist D))
            (fastCauchyNormalFormDecodeBHist (fastCauchyNormalFormEncodeBHist S))
            (fastCauchyNormalFormDecodeBHist (fastCauchyNormalFormEncodeBHist R))
            (fastCauchyNormalFormDecodeBHist (fastCauchyNormalFormEncodeBHist E))
            (fastCauchyNormalFormDecodeBHist (fastCauchyNormalFormEncodeBHist C))
            (fastCauchyNormalFormDecodeBHist (fastCauchyNormalFormEncodeBHist H))
            (fastCauchyNormalFormDecodeBHist (fastCauchyNormalFormEncodeBHist Q))
            (fastCauchyNormalFormDecodeBHist (fastCauchyNormalFormEncodeBHist P))
            (fastCauchyNormalFormDecodeBHist (fastCauchyNormalFormEncodeBHist N))) =
          some (FastCauchyNormalFormUp.mk D S R E C H Q P N)
      rw [FastCauchyNormalFormTasteGate_single_carrier_alignment_decode_encode D,
        FastCauchyNormalFormTasteGate_single_carrier_alignment_decode_encode S,
        FastCauchyNormalFormTasteGate_single_carrier_alignment_decode_encode R,
        FastCauchyNormalFormTasteGate_single_carrier_alignment_decode_encode E,
        FastCauchyNormalFormTasteGate_single_carrier_alignment_decode_encode C,
        FastCauchyNormalFormTasteGate_single_carrier_alignment_decode_encode H,
        FastCauchyNormalFormTasteGate_single_carrier_alignment_decode_encode Q,
        FastCauchyNormalFormTasteGate_single_carrier_alignment_decode_encode P,
        FastCauchyNormalFormTasteGate_single_carrier_alignment_decode_encode N]

private theorem FastCauchyNormalFormTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FastCauchyNormalFormUp} :
    fastCauchyNormalFormToEventFlow x = fastCauchyNormalFormToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fastCauchyNormalFormFromEventFlow (fastCauchyNormalFormToEventFlow x) =
        fastCauchyNormalFormFromEventFlow (fastCauchyNormalFormToEventFlow y) :=
    congrArg fastCauchyNormalFormFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FastCauchyNormalFormTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FastCauchyNormalFormTasteGate_single_carrier_alignment_round_trip y)))

instance fastCauchyNormalFormBHistCarrier : BHistCarrier FastCauchyNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fastCauchyNormalFormToEventFlow
  fromEventFlow := fastCauchyNormalFormFromEventFlow

instance fastCauchyNormalFormChapterTasteGate : ChapterTasteGate FastCauchyNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fastCauchyNormalFormFromEventFlow (fastCauchyNormalFormToEventFlow x) = some x
    exact FastCauchyNormalFormTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FastCauchyNormalFormTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem FastCauchyNormalFormTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FastCauchyNormalFormUp) ∧
      Nonempty (BHistCarrier FastCauchyNormalFormUp) ∧
      (∀ h : BHist,
        fastCauchyNormalFormDecodeBHist (fastCauchyNormalFormEncodeBHist h) = h) ∧
      fastCauchyNormalFormEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨fastCauchyNormalFormChapterTasteGate⟩,
      ⟨fastCauchyNormalFormBHistCarrier⟩,
      FastCauchyNormalFormTasteGate_single_carrier_alignment_decode_encode,
      rfl⟩

end BEDC.Derived.FastCauchyNormalFormUp
