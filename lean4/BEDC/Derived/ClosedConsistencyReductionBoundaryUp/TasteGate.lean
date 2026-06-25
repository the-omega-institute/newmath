import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedConsistencyReductionBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Closed-consistency reduction-boundary packet over ten displayed BEDC rows. -/
inductive ClosedConsistencyReductionBoundaryUp : Type where
  | mk : (S Q E D K O H C P N : BHist) → ClosedConsistencyReductionBoundaryUp
  deriving DecidableEq

def closedConsistencyReductionBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedConsistencyReductionBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedConsistencyReductionBoundaryEncodeBHist h

def closedConsistencyReductionBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedConsistencyReductionBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedConsistencyReductionBoundaryDecodeBHist tail)

private theorem ClosedConsistencyReductionBoundaryUp_decode_encode :
    ∀ h : BHist,
      closedConsistencyReductionBoundaryDecodeBHist
          (closedConsistencyReductionBoundaryEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def closedConsistencyReductionBoundaryFields :
    ClosedConsistencyReductionBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedConsistencyReductionBoundaryUp.mk S Q E D K O H C P N =>
      [S, Q, E, D, K, O, H, C, P, N]

def closedConsistencyReductionBoundaryToEventFlow :
    ClosedConsistencyReductionBoundaryUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (closedConsistencyReductionBoundaryFields x).map
    closedConsistencyReductionBoundaryEncodeBHist

private def closedConsistencyReductionBoundaryEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      closedConsistencyReductionBoundaryEventAtDefault index rest

def closedConsistencyReductionBoundaryFromEventFlow
    (ef : EventFlow) : Option ClosedConsistencyReductionBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ClosedConsistencyReductionBoundaryUp.mk
      (closedConsistencyReductionBoundaryDecodeBHist
        (closedConsistencyReductionBoundaryEventAtDefault 0 ef))
      (closedConsistencyReductionBoundaryDecodeBHist
        (closedConsistencyReductionBoundaryEventAtDefault 1 ef))
      (closedConsistencyReductionBoundaryDecodeBHist
        (closedConsistencyReductionBoundaryEventAtDefault 2 ef))
      (closedConsistencyReductionBoundaryDecodeBHist
        (closedConsistencyReductionBoundaryEventAtDefault 3 ef))
      (closedConsistencyReductionBoundaryDecodeBHist
        (closedConsistencyReductionBoundaryEventAtDefault 4 ef))
      (closedConsistencyReductionBoundaryDecodeBHist
        (closedConsistencyReductionBoundaryEventAtDefault 5 ef))
      (closedConsistencyReductionBoundaryDecodeBHist
        (closedConsistencyReductionBoundaryEventAtDefault 6 ef))
      (closedConsistencyReductionBoundaryDecodeBHist
        (closedConsistencyReductionBoundaryEventAtDefault 7 ef))
      (closedConsistencyReductionBoundaryDecodeBHist
        (closedConsistencyReductionBoundaryEventAtDefault 8 ef))
      (closedConsistencyReductionBoundaryDecodeBHist
        (closedConsistencyReductionBoundaryEventAtDefault 9 ef)))

private theorem ClosedConsistencyReductionBoundaryUp_round_trip :
    ∀ x : ClosedConsistencyReductionBoundaryUp,
      closedConsistencyReductionBoundaryFromEventFlow
          (closedConsistencyReductionBoundaryToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S Q E D K O H C P N =>
      change
        some
            (ClosedConsistencyReductionBoundaryUp.mk
              (closedConsistencyReductionBoundaryDecodeBHist
                (closedConsistencyReductionBoundaryEncodeBHist S))
              (closedConsistencyReductionBoundaryDecodeBHist
                (closedConsistencyReductionBoundaryEncodeBHist Q))
              (closedConsistencyReductionBoundaryDecodeBHist
                (closedConsistencyReductionBoundaryEncodeBHist E))
              (closedConsistencyReductionBoundaryDecodeBHist
                (closedConsistencyReductionBoundaryEncodeBHist D))
              (closedConsistencyReductionBoundaryDecodeBHist
                (closedConsistencyReductionBoundaryEncodeBHist K))
              (closedConsistencyReductionBoundaryDecodeBHist
                (closedConsistencyReductionBoundaryEncodeBHist O))
              (closedConsistencyReductionBoundaryDecodeBHist
                (closedConsistencyReductionBoundaryEncodeBHist H))
              (closedConsistencyReductionBoundaryDecodeBHist
                (closedConsistencyReductionBoundaryEncodeBHist C))
              (closedConsistencyReductionBoundaryDecodeBHist
                (closedConsistencyReductionBoundaryEncodeBHist P))
              (closedConsistencyReductionBoundaryDecodeBHist
                (closedConsistencyReductionBoundaryEncodeBHist N))) =
          some (ClosedConsistencyReductionBoundaryUp.mk S Q E D K O H C P N)
      rw [ClosedConsistencyReductionBoundaryUp_decode_encode S,
        ClosedConsistencyReductionBoundaryUp_decode_encode Q,
        ClosedConsistencyReductionBoundaryUp_decode_encode E,
        ClosedConsistencyReductionBoundaryUp_decode_encode D,
        ClosedConsistencyReductionBoundaryUp_decode_encode K,
        ClosedConsistencyReductionBoundaryUp_decode_encode O,
        ClosedConsistencyReductionBoundaryUp_decode_encode H,
        ClosedConsistencyReductionBoundaryUp_decode_encode C,
        ClosedConsistencyReductionBoundaryUp_decode_encode P,
        ClosedConsistencyReductionBoundaryUp_decode_encode N]

private theorem ClosedConsistencyReductionBoundaryUp_toEventFlow_injective
    {x y : ClosedConsistencyReductionBoundaryUp} :
    closedConsistencyReductionBoundaryToEventFlow x =
        closedConsistencyReductionBoundaryToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedConsistencyReductionBoundaryFromEventFlow
          (closedConsistencyReductionBoundaryToEventFlow x) =
        closedConsistencyReductionBoundaryFromEventFlow
          (closedConsistencyReductionBoundaryToEventFlow y) :=
    congrArg closedConsistencyReductionBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ClosedConsistencyReductionBoundaryUp_round_trip x).symm
      (Eq.trans hread (ClosedConsistencyReductionBoundaryUp_round_trip y)))

private theorem ClosedConsistencyReductionBoundaryUp_fields_faithful :
    ∀ x y : ClosedConsistencyReductionBoundaryUp,
      closedConsistencyReductionBoundaryFields x =
          closedConsistencyReductionBoundaryFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S Q E D K O H C P N =>
      cases y with
      | mk S' Q' E' D' K' O' H' C' P' N' =>
          cases hfields
          rfl

instance closedConsistencyReductionBoundaryBHistCarrier :
    BHistCarrier ClosedConsistencyReductionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedConsistencyReductionBoundaryToEventFlow
  fromEventFlow := closedConsistencyReductionBoundaryFromEventFlow

instance closedConsistencyReductionBoundaryChapterTasteGate :
    ChapterTasteGate ClosedConsistencyReductionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedConsistencyReductionBoundaryFromEventFlow
          (closedConsistencyReductionBoundaryToEventFlow x) =
        some x
    exact ClosedConsistencyReductionBoundaryUp_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ClosedConsistencyReductionBoundaryUp_toEventFlow_injective heq)

instance closedConsistencyReductionBoundaryFieldFaithful :
    FieldFaithful ClosedConsistencyReductionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := closedConsistencyReductionBoundaryFields
  field_faithful := ClosedConsistencyReductionBoundaryUp_fields_faithful

instance closedConsistencyReductionBoundaryNontrivial :
    BEDC.Meta.TasteGate.Nontrivial ClosedConsistencyReductionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClosedConsistencyReductionBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      ClosedConsistencyReductionBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ClosedConsistencyReductionBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  closedConsistencyReductionBoundaryChapterTasteGate

end BEDC.Derived.ClosedConsistencyReductionBoundaryUp
