import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OscillationDerivativeUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OscillationDerivativeUp : Type where
  | mk (F X W O R H C P N : BHist) : OscillationDerivativeUp

def oscillationDerivativeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: oscillationDerivativeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: oscillationDerivativeEncodeBHist h

def oscillationDerivativeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (oscillationDerivativeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (oscillationDerivativeDecodeBHist tail)

private theorem OscillationDerivativeTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      oscillationDerivativeDecodeBHist (oscillationDerivativeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def oscillationDerivativeFields : OscillationDerivativeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OscillationDerivativeUp.mk F X W O R H C P N => [F, X, W, O, R, H, C, P, N]

def oscillationDerivativeToEventFlow : OscillationDerivativeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (oscillationDerivativeFields x).map oscillationDerivativeEncodeBHist

private def oscillationDerivativeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => oscillationDerivativeEventAtDefault index rest

def oscillationDerivativeFromEventFlow :
    EventFlow → Option OscillationDerivativeUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (OscillationDerivativeUp.mk
          (oscillationDerivativeDecodeBHist (oscillationDerivativeEventAtDefault 0 ef))
          (oscillationDerivativeDecodeBHist (oscillationDerivativeEventAtDefault 1 ef))
          (oscillationDerivativeDecodeBHist (oscillationDerivativeEventAtDefault 2 ef))
          (oscillationDerivativeDecodeBHist (oscillationDerivativeEventAtDefault 3 ef))
          (oscillationDerivativeDecodeBHist (oscillationDerivativeEventAtDefault 4 ef))
          (oscillationDerivativeDecodeBHist (oscillationDerivativeEventAtDefault 5 ef))
          (oscillationDerivativeDecodeBHist (oscillationDerivativeEventAtDefault 6 ef))
          (oscillationDerivativeDecodeBHist (oscillationDerivativeEventAtDefault 7 ef))
          (oscillationDerivativeDecodeBHist (oscillationDerivativeEventAtDefault 8 ef)))

private theorem OscillationDerivativeTasteGate_single_carrier_alignment_round_trip
    (x : OscillationDerivativeUp) :
    oscillationDerivativeFromEventFlow (oscillationDerivativeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F X W O R H C P N =>
      change
        some
          (OscillationDerivativeUp.mk
            (oscillationDerivativeDecodeBHist (oscillationDerivativeEncodeBHist F))
            (oscillationDerivativeDecodeBHist (oscillationDerivativeEncodeBHist X))
            (oscillationDerivativeDecodeBHist (oscillationDerivativeEncodeBHist W))
            (oscillationDerivativeDecodeBHist (oscillationDerivativeEncodeBHist O))
            (oscillationDerivativeDecodeBHist (oscillationDerivativeEncodeBHist R))
            (oscillationDerivativeDecodeBHist (oscillationDerivativeEncodeBHist H))
            (oscillationDerivativeDecodeBHist (oscillationDerivativeEncodeBHist C))
            (oscillationDerivativeDecodeBHist (oscillationDerivativeEncodeBHist P))
            (oscillationDerivativeDecodeBHist (oscillationDerivativeEncodeBHist N))) =
          some (OscillationDerivativeUp.mk F X W O R H C P N)
      rw [OscillationDerivativeTasteGate_single_carrier_alignment_decode F,
        OscillationDerivativeTasteGate_single_carrier_alignment_decode X,
        OscillationDerivativeTasteGate_single_carrier_alignment_decode W,
        OscillationDerivativeTasteGate_single_carrier_alignment_decode O,
        OscillationDerivativeTasteGate_single_carrier_alignment_decode R,
        OscillationDerivativeTasteGate_single_carrier_alignment_decode H,
        OscillationDerivativeTasteGate_single_carrier_alignment_decode C,
        OscillationDerivativeTasteGate_single_carrier_alignment_decode P,
        OscillationDerivativeTasteGate_single_carrier_alignment_decode N]

private theorem OscillationDerivativeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : OscillationDerivativeUp} :
    oscillationDerivativeToEventFlow x = oscillationDerivativeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      oscillationDerivativeFromEventFlow (oscillationDerivativeToEventFlow x) =
        oscillationDerivativeFromEventFlow (oscillationDerivativeToEventFlow y) :=
    congrArg oscillationDerivativeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (OscillationDerivativeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (OscillationDerivativeTasteGate_single_carrier_alignment_round_trip y)))

instance oscillationDerivativeBHistCarrier :
    BHistCarrier OscillationDerivativeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := oscillationDerivativeToEventFlow
  fromEventFlow := oscillationDerivativeFromEventFlow

instance oscillationDerivativeChapterTasteGate :
    ChapterTasteGate OscillationDerivativeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change oscillationDerivativeFromEventFlow (oscillationDerivativeToEventFlow x) = some x
    exact OscillationDerivativeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (OscillationDerivativeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate OscillationDerivativeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  oscillationDerivativeChapterTasteGate

theorem OscillationDerivativeTasteGate_single_carrier_alignment :
    (∀ h : BHist, oscillationDerivativeDecodeBHist (oscillationDerivativeEncodeBHist h) = h) ∧
      (∀ x : OscillationDerivativeUp,
        oscillationDerivativeFromEventFlow (oscillationDerivativeToEventFlow x) = some x) ∧
        (∀ x y : OscillationDerivativeUp,
          oscillationDerivativeToEventFlow x = oscillationDerivativeToEventFlow y → x = y) ∧
          oscillationDerivativeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact OscillationDerivativeTasteGate_single_carrier_alignment_decode
  · constructor
    · exact OscillationDerivativeTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact OscillationDerivativeTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.OscillationDerivativeUp.TasteGate
