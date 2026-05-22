import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyDistanceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyDistanceUp : Type where
  | mk (X Y S T D Q E H C P N : BHist) : RegularCauchyDistanceUp
  deriving DecidableEq

def regularCauchyDistanceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyDistanceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyDistanceEncodeBHist h

def regularCauchyDistanceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyDistanceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyDistanceDecodeBHist tail)

private theorem regularCauchyDistance_decode_encode_bhist :
    ∀ h : BHist, regularCauchyDistanceDecodeBHist (regularCauchyDistanceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyDistanceFields : RegularCauchyDistanceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyDistanceUp.mk X Y S T D Q E H C P N => [X, Y, S, T, D, Q, E, H, C, P, N]

def regularCauchyDistanceToEventFlow : RegularCauchyDistanceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (regularCauchyDistanceFields x).map regularCauchyDistanceEncodeBHist

private def regularCauchyDistanceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyDistanceEventAtDefault index rest

def regularCauchyDistanceFromEventFlow (ef : EventFlow) : Option RegularCauchyDistanceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyDistanceUp.mk
      (regularCauchyDistanceDecodeBHist (regularCauchyDistanceEventAtDefault 0 ef))
      (regularCauchyDistanceDecodeBHist (regularCauchyDistanceEventAtDefault 1 ef))
      (regularCauchyDistanceDecodeBHist (regularCauchyDistanceEventAtDefault 2 ef))
      (regularCauchyDistanceDecodeBHist (regularCauchyDistanceEventAtDefault 3 ef))
      (regularCauchyDistanceDecodeBHist (regularCauchyDistanceEventAtDefault 4 ef))
      (regularCauchyDistanceDecodeBHist (regularCauchyDistanceEventAtDefault 5 ef))
      (regularCauchyDistanceDecodeBHist (regularCauchyDistanceEventAtDefault 6 ef))
      (regularCauchyDistanceDecodeBHist (regularCauchyDistanceEventAtDefault 7 ef))
      (regularCauchyDistanceDecodeBHist (regularCauchyDistanceEventAtDefault 8 ef))
      (regularCauchyDistanceDecodeBHist (regularCauchyDistanceEventAtDefault 9 ef))
      (regularCauchyDistanceDecodeBHist (regularCauchyDistanceEventAtDefault 10 ef)))

private theorem regularCauchyDistance_round_trip :
    ∀ x : RegularCauchyDistanceUp,
      regularCauchyDistanceFromEventFlow (regularCauchyDistanceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y S T D Q E H C P N =>
      change
        some
          (RegularCauchyDistanceUp.mk
            (regularCauchyDistanceDecodeBHist (regularCauchyDistanceEncodeBHist X))
            (regularCauchyDistanceDecodeBHist (regularCauchyDistanceEncodeBHist Y))
            (regularCauchyDistanceDecodeBHist (regularCauchyDistanceEncodeBHist S))
            (regularCauchyDistanceDecodeBHist (regularCauchyDistanceEncodeBHist T))
            (regularCauchyDistanceDecodeBHist (regularCauchyDistanceEncodeBHist D))
            (regularCauchyDistanceDecodeBHist (regularCauchyDistanceEncodeBHist Q))
            (regularCauchyDistanceDecodeBHist (regularCauchyDistanceEncodeBHist E))
            (regularCauchyDistanceDecodeBHist (regularCauchyDistanceEncodeBHist H))
            (regularCauchyDistanceDecodeBHist (regularCauchyDistanceEncodeBHist C))
            (regularCauchyDistanceDecodeBHist (regularCauchyDistanceEncodeBHist P))
            (regularCauchyDistanceDecodeBHist (regularCauchyDistanceEncodeBHist N))) =
          some (RegularCauchyDistanceUp.mk X Y S T D Q E H C P N)
      rw [regularCauchyDistance_decode_encode_bhist X,
        regularCauchyDistance_decode_encode_bhist Y,
        regularCauchyDistance_decode_encode_bhist S,
        regularCauchyDistance_decode_encode_bhist T,
        regularCauchyDistance_decode_encode_bhist D,
        regularCauchyDistance_decode_encode_bhist Q,
        regularCauchyDistance_decode_encode_bhist E,
        regularCauchyDistance_decode_encode_bhist H,
        regularCauchyDistance_decode_encode_bhist C,
        regularCauchyDistance_decode_encode_bhist P,
        regularCauchyDistance_decode_encode_bhist N]

private theorem regularCauchyDistanceToEventFlow_injective
    {x y : RegularCauchyDistanceUp} :
    regularCauchyDistanceToEventFlow x = regularCauchyDistanceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyDistanceFromEventFlow (regularCauchyDistanceToEventFlow x) =
        regularCauchyDistanceFromEventFlow (regularCauchyDistanceToEventFlow y) :=
    congrArg regularCauchyDistanceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyDistance_round_trip x).symm
      (Eq.trans hread (regularCauchyDistance_round_trip y)))

instance regularCauchyDistanceBHistCarrier : BHistCarrier RegularCauchyDistanceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyDistanceToEventFlow
  fromEventFlow := regularCauchyDistanceFromEventFlow

instance regularCauchyDistanceChapterTasteGate : ChapterTasteGate RegularCauchyDistanceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyDistanceFromEventFlow (regularCauchyDistanceToEventFlow x) = some x
    exact regularCauchyDistance_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyDistanceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyDistanceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyDistanceChapterTasteGate

theorem RegularCauchyDistanceTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularCauchyDistanceDecodeBHist (regularCauchyDistanceEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyDistanceUp,
        regularCauchyDistanceFromEventFlow (regularCauchyDistanceToEventFlow x) = some x) ∧
      (∀ x y : RegularCauchyDistanceUp,
        regularCauchyDistanceToEventFlow x = regularCauchyDistanceToEventFlow y → x = y) ∧
      regularCauchyDistanceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨regularCauchyDistance_decode_encode_bhist,
      regularCauchyDistance_round_trip,
      (fun _ _ heq => regularCauchyDistanceToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyDistanceUp
