import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyFunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyFunctorUp : Type where
  | mk (S T M R Q H C P N : BHist) : RegularCauchyFunctorUp
  deriving DecidableEq

def regularCauchyFunctorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyFunctorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyFunctorEncodeBHist h

def regularCauchyFunctorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyFunctorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyFunctorDecodeBHist tail)

private theorem RegularCauchyFunctorTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchyFunctorDecodeBHist (regularCauchyFunctorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyFunctorFields : RegularCauchyFunctorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyFunctorUp.mk S T M R Q H C P N => [S, T, M, R, Q, H, C, P, N]

def regularCauchyFunctorToEventFlow : RegularCauchyFunctorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyFunctorFields x).map regularCauchyFunctorEncodeBHist

private def regularCauchyFunctorEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyFunctorEventAtDefault index rest

def regularCauchyFunctorFromEventFlow (ef : EventFlow) :
    Option RegularCauchyFunctorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyFunctorUp.mk
      (regularCauchyFunctorDecodeBHist (regularCauchyFunctorEventAtDefault 0 ef))
      (regularCauchyFunctorDecodeBHist (regularCauchyFunctorEventAtDefault 1 ef))
      (regularCauchyFunctorDecodeBHist (regularCauchyFunctorEventAtDefault 2 ef))
      (regularCauchyFunctorDecodeBHist (regularCauchyFunctorEventAtDefault 3 ef))
      (regularCauchyFunctorDecodeBHist (regularCauchyFunctorEventAtDefault 4 ef))
      (regularCauchyFunctorDecodeBHist (regularCauchyFunctorEventAtDefault 5 ef))
      (regularCauchyFunctorDecodeBHist (regularCauchyFunctorEventAtDefault 6 ef))
      (regularCauchyFunctorDecodeBHist (regularCauchyFunctorEventAtDefault 7 ef))
      (regularCauchyFunctorDecodeBHist (regularCauchyFunctorEventAtDefault 8 ef)))

private theorem RegularCauchyFunctorTasteGate_single_carrier_alignment_round_trip
    (x : RegularCauchyFunctorUp) :
    regularCauchyFunctorFromEventFlow (regularCauchyFunctorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S T M R Q H C P N =>
      change
        some
          (RegularCauchyFunctorUp.mk
            (regularCauchyFunctorDecodeBHist (regularCauchyFunctorEncodeBHist S))
            (regularCauchyFunctorDecodeBHist (regularCauchyFunctorEncodeBHist T))
            (regularCauchyFunctorDecodeBHist (regularCauchyFunctorEncodeBHist M))
            (regularCauchyFunctorDecodeBHist (regularCauchyFunctorEncodeBHist R))
            (regularCauchyFunctorDecodeBHist (regularCauchyFunctorEncodeBHist Q))
            (regularCauchyFunctorDecodeBHist (regularCauchyFunctorEncodeBHist H))
            (regularCauchyFunctorDecodeBHist (regularCauchyFunctorEncodeBHist C))
            (regularCauchyFunctorDecodeBHist (regularCauchyFunctorEncodeBHist P))
            (regularCauchyFunctorDecodeBHist (regularCauchyFunctorEncodeBHist N))) =
          some (RegularCauchyFunctorUp.mk S T M R Q H C P N)
      rw [RegularCauchyFunctorTasteGate_single_carrier_alignment_decode_encode S,
        RegularCauchyFunctorTasteGate_single_carrier_alignment_decode_encode T,
        RegularCauchyFunctorTasteGate_single_carrier_alignment_decode_encode M,
        RegularCauchyFunctorTasteGate_single_carrier_alignment_decode_encode R,
        RegularCauchyFunctorTasteGate_single_carrier_alignment_decode_encode Q,
        RegularCauchyFunctorTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyFunctorTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyFunctorTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchyFunctorTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchyFunctorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyFunctorUp} :
    regularCauchyFunctorToEventFlow x = regularCauchyFunctorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyFunctorFromEventFlow (regularCauchyFunctorToEventFlow x) =
        regularCauchyFunctorFromEventFlow (regularCauchyFunctorToEventFlow y) :=
    congrArg regularCauchyFunctorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegularCauchyFunctorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RegularCauchyFunctorTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyFunctorBHistCarrier : BHistCarrier RegularCauchyFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyFunctorToEventFlow
  fromEventFlow := regularCauchyFunctorFromEventFlow

instance regularCauchyFunctorChapterTasteGate :
    ChapterTasteGate RegularCauchyFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyFunctorFromEventFlow (regularCauchyFunctorToEventFlow x) = some x
    exact RegularCauchyFunctorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyFunctorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RegularCauchyFunctorTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularCauchyFunctorDecodeBHist (regularCauchyFunctorEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyFunctorUp,
        regularCauchyFunctorFromEventFlow (regularCauchyFunctorToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyFunctorUp,
          regularCauchyFunctorToEventFlow x = regularCauchyFunctorToEventFlow y → x = y) ∧
          regularCauchyFunctorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegularCauchyFunctorTasteGate_single_carrier_alignment_decode_encode,
      RegularCauchyFunctorTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RegularCauchyFunctorTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyFunctorUp
