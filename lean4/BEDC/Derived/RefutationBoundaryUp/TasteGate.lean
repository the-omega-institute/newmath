import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RefutationBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RefutationBoundaryUp : Type where
  | mk (A F D S T H C P N : BHist) : RefutationBoundaryUp
  deriving DecidableEq

def refutationBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: refutationBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: refutationBoundaryEncodeBHist h

def refutationBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (refutationBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (refutationBoundaryDecodeBHist tail)

private theorem refutationBoundaryDecode_encode_bhist :
    ∀ h : BHist,
      refutationBoundaryDecodeBHist (refutationBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def refutationBoundaryFields : RefutationBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RefutationBoundaryUp.mk A F D S T H C P N => [A, F, D, S, T, H, C, P, N]

def refutationBoundaryToEventFlow : RefutationBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map refutationBoundaryEncodeBHist (refutationBoundaryFields x)

private def refutationBoundaryEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => refutationBoundaryEventAtDefault index rest

def refutationBoundaryFromEventFlow (ef : EventFlow) : Option RefutationBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RefutationBoundaryUp.mk
      (refutationBoundaryDecodeBHist (refutationBoundaryEventAtDefault 0 ef))
      (refutationBoundaryDecodeBHist (refutationBoundaryEventAtDefault 1 ef))
      (refutationBoundaryDecodeBHist (refutationBoundaryEventAtDefault 2 ef))
      (refutationBoundaryDecodeBHist (refutationBoundaryEventAtDefault 3 ef))
      (refutationBoundaryDecodeBHist (refutationBoundaryEventAtDefault 4 ef))
      (refutationBoundaryDecodeBHist (refutationBoundaryEventAtDefault 5 ef))
      (refutationBoundaryDecodeBHist (refutationBoundaryEventAtDefault 6 ef))
      (refutationBoundaryDecodeBHist (refutationBoundaryEventAtDefault 7 ef))
      (refutationBoundaryDecodeBHist (refutationBoundaryEventAtDefault 8 ef)))

private theorem refutationBoundary_round_trip :
    ∀ x : RefutationBoundaryUp,
      refutationBoundaryFromEventFlow (refutationBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A F D S T H C P N =>
      change
        some
          (RefutationBoundaryUp.mk
            (refutationBoundaryDecodeBHist (refutationBoundaryEncodeBHist A))
            (refutationBoundaryDecodeBHist (refutationBoundaryEncodeBHist F))
            (refutationBoundaryDecodeBHist (refutationBoundaryEncodeBHist D))
            (refutationBoundaryDecodeBHist (refutationBoundaryEncodeBHist S))
            (refutationBoundaryDecodeBHist (refutationBoundaryEncodeBHist T))
            (refutationBoundaryDecodeBHist (refutationBoundaryEncodeBHist H))
            (refutationBoundaryDecodeBHist (refutationBoundaryEncodeBHist C))
            (refutationBoundaryDecodeBHist (refutationBoundaryEncodeBHist P))
            (refutationBoundaryDecodeBHist (refutationBoundaryEncodeBHist N))) =
          some (RefutationBoundaryUp.mk A F D S T H C P N)
      rw [refutationBoundaryDecode_encode_bhist A,
        refutationBoundaryDecode_encode_bhist F,
        refutationBoundaryDecode_encode_bhist D,
        refutationBoundaryDecode_encode_bhist S,
        refutationBoundaryDecode_encode_bhist T,
        refutationBoundaryDecode_encode_bhist H,
        refutationBoundaryDecode_encode_bhist C,
        refutationBoundaryDecode_encode_bhist P,
        refutationBoundaryDecode_encode_bhist N]

private theorem refutationBoundaryToEventFlow_injective {x y : RefutationBoundaryUp} :
    refutationBoundaryToEventFlow x = refutationBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      refutationBoundaryFromEventFlow (refutationBoundaryToEventFlow x) =
        refutationBoundaryFromEventFlow (refutationBoundaryToEventFlow y) :=
    congrArg refutationBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (refutationBoundary_round_trip x).symm
      (Eq.trans hread (refutationBoundary_round_trip y)))

instance refutationBoundaryBHistCarrier : BHistCarrier RefutationBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := refutationBoundaryToEventFlow
  fromEventFlow := refutationBoundaryFromEventFlow

instance refutationBoundaryChapterTasteGate : ChapterTasteGate RefutationBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change refutationBoundaryFromEventFlow (refutationBoundaryToEventFlow x) = some x
    exact refutationBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (refutationBoundaryToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RefutationBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  refutationBoundaryChapterTasteGate

theorem RefutationBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist, refutationBoundaryDecodeBHist (refutationBoundaryEncodeBHist h) = h) ∧
      (∀ x : RefutationBoundaryUp,
        refutationBoundaryFromEventFlow (refutationBoundaryToEventFlow x) = some x) ∧
      (∀ x y : RefutationBoundaryUp,
        refutationBoundaryToEventFlow x = refutationBoundaryToEventFlow y → x = y) ∧
      refutationBoundaryEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact refutationBoundaryDecode_encode_bhist
  · constructor
    · exact refutationBoundary_round_trip
    · constructor
      · intro x y heq
        exact refutationBoundaryToEventFlow_injective heq
      · rfl

end BEDC.Derived.RefutationBoundaryUp
