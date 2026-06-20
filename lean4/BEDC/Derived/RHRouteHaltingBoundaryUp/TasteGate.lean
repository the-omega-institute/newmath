import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RHRouteHaltingBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RHRouteHaltingBoundaryUp : Type where
  | mk (R G D F Z H C P N : BHist) : RHRouteHaltingBoundaryUp
  deriving DecidableEq

def rhRouteHaltingBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rhRouteHaltingBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rhRouteHaltingBoundaryEncodeBHist h

def rhRouteHaltingBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rhRouteHaltingBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rhRouteHaltingBoundaryDecodeBHist tail)

private theorem rhRouteHaltingBoundary_decode_encode_bhist :
    ∀ h : BHist, rhRouteHaltingBoundaryDecodeBHist (rhRouteHaltingBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def rhRouteHaltingBoundaryFields : RHRouteHaltingBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RHRouteHaltingBoundaryUp.mk R G D F Z H C P N => [R, G, D, F, Z, H, C, P, N]

def rhRouteHaltingBoundaryToEventFlow : RHRouteHaltingBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (rhRouteHaltingBoundaryFields x).map rhRouteHaltingBoundaryEncodeBHist

private def rhRouteHaltingBoundaryEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => rhRouteHaltingBoundaryEventAtDefault index rest

def rhRouteHaltingBoundaryFromEventFlow
    (ef : EventFlow) : Option RHRouteHaltingBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RHRouteHaltingBoundaryUp.mk
      (rhRouteHaltingBoundaryDecodeBHist (rhRouteHaltingBoundaryEventAtDefault 0 ef))
      (rhRouteHaltingBoundaryDecodeBHist (rhRouteHaltingBoundaryEventAtDefault 1 ef))
      (rhRouteHaltingBoundaryDecodeBHist (rhRouteHaltingBoundaryEventAtDefault 2 ef))
      (rhRouteHaltingBoundaryDecodeBHist (rhRouteHaltingBoundaryEventAtDefault 3 ef))
      (rhRouteHaltingBoundaryDecodeBHist (rhRouteHaltingBoundaryEventAtDefault 4 ef))
      (rhRouteHaltingBoundaryDecodeBHist (rhRouteHaltingBoundaryEventAtDefault 5 ef))
      (rhRouteHaltingBoundaryDecodeBHist (rhRouteHaltingBoundaryEventAtDefault 6 ef))
      (rhRouteHaltingBoundaryDecodeBHist (rhRouteHaltingBoundaryEventAtDefault 7 ef))
      (rhRouteHaltingBoundaryDecodeBHist (rhRouteHaltingBoundaryEventAtDefault 8 ef)))

private theorem rhRouteHaltingBoundary_round_trip :
    ∀ x : RHRouteHaltingBoundaryUp,
      rhRouteHaltingBoundaryFromEventFlow (rhRouteHaltingBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R G D F Z H C P N =>
      change
        some
          (RHRouteHaltingBoundaryUp.mk
            (rhRouteHaltingBoundaryDecodeBHist (rhRouteHaltingBoundaryEncodeBHist R))
            (rhRouteHaltingBoundaryDecodeBHist (rhRouteHaltingBoundaryEncodeBHist G))
            (rhRouteHaltingBoundaryDecodeBHist (rhRouteHaltingBoundaryEncodeBHist D))
            (rhRouteHaltingBoundaryDecodeBHist (rhRouteHaltingBoundaryEncodeBHist F))
            (rhRouteHaltingBoundaryDecodeBHist (rhRouteHaltingBoundaryEncodeBHist Z))
            (rhRouteHaltingBoundaryDecodeBHist (rhRouteHaltingBoundaryEncodeBHist H))
            (rhRouteHaltingBoundaryDecodeBHist (rhRouteHaltingBoundaryEncodeBHist C))
            (rhRouteHaltingBoundaryDecodeBHist (rhRouteHaltingBoundaryEncodeBHist P))
            (rhRouteHaltingBoundaryDecodeBHist (rhRouteHaltingBoundaryEncodeBHist N))) =
          some (RHRouteHaltingBoundaryUp.mk R G D F Z H C P N)
      rw [rhRouteHaltingBoundary_decode_encode_bhist R,
        rhRouteHaltingBoundary_decode_encode_bhist G,
        rhRouteHaltingBoundary_decode_encode_bhist D,
        rhRouteHaltingBoundary_decode_encode_bhist F,
        rhRouteHaltingBoundary_decode_encode_bhist Z,
        rhRouteHaltingBoundary_decode_encode_bhist H,
        rhRouteHaltingBoundary_decode_encode_bhist C,
        rhRouteHaltingBoundary_decode_encode_bhist P,
        rhRouteHaltingBoundary_decode_encode_bhist N]

private theorem rhRouteHaltingBoundaryToEventFlow_injective
    {x y : RHRouteHaltingBoundaryUp} :
    rhRouteHaltingBoundaryToEventFlow x = rhRouteHaltingBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rhRouteHaltingBoundaryFromEventFlow (rhRouteHaltingBoundaryToEventFlow x) =
        rhRouteHaltingBoundaryFromEventFlow (rhRouteHaltingBoundaryToEventFlow y) :=
    congrArg rhRouteHaltingBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (rhRouteHaltingBoundary_round_trip x).symm
      (Eq.trans hread (rhRouteHaltingBoundary_round_trip y)))

instance rhRouteHaltingBoundaryBHistCarrier :
    BHistCarrier RHRouteHaltingBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rhRouteHaltingBoundaryToEventFlow
  fromEventFlow := rhRouteHaltingBoundaryFromEventFlow

instance rhRouteHaltingBoundaryChapterTasteGate :
    ChapterTasteGate RHRouteHaltingBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      rhRouteHaltingBoundaryFromEventFlow (rhRouteHaltingBoundaryToEventFlow x) =
        some x
    exact rhRouteHaltingBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (rhRouteHaltingBoundaryToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RHRouteHaltingBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  rhRouteHaltingBoundaryChapterTasteGate

theorem RHRouteHaltingBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist, rhRouteHaltingBoundaryDecodeBHist (rhRouteHaltingBoundaryEncodeBHist h) = h) ∧
      (∀ x : RHRouteHaltingBoundaryUp,
        rhRouteHaltingBoundaryFromEventFlow (rhRouteHaltingBoundaryToEventFlow x) = some x) ∧
        (∀ x y : RHRouteHaltingBoundaryUp,
          rhRouteHaltingBoundaryToEventFlow x = rhRouteHaltingBoundaryToEventFlow y -> x = y) ∧
          rhRouteHaltingBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨rhRouteHaltingBoundary_decode_encode_bhist,
      rhRouteHaltingBoundary_round_trip,
      (fun _ _ heq => rhRouteHaltingBoundaryToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RHRouteHaltingBoundaryUp
