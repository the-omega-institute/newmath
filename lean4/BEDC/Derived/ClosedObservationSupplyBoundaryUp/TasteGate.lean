import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedObservationSupplyBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedObservationSupplyBoundaryUp : Type where
  | mk (R Q G F A H C P N : BHist) : ClosedObservationSupplyBoundaryUp
  deriving DecidableEq

def closedObservationSupplyBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedObservationSupplyBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedObservationSupplyBoundaryEncodeBHist h

def closedObservationSupplyBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedObservationSupplyBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedObservationSupplyBoundaryDecodeBHist tail)

private theorem closedObservationSupplyBoundary_decode_encode_bhist :
    ∀ h : BHist,
      closedObservationSupplyBoundaryDecodeBHist
        (closedObservationSupplyBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem closedObservationSupplyBoundary_mk_congr
    {R R' Q Q' G G' F F' A A' H H' C C' P P' N N' : BHist}
    (hR : R' = R)
    (hQ : Q' = Q)
    (hG : G' = G)
    (hF : F' = F)
    (hA : A' = A)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    ClosedObservationSupplyBoundaryUp.mk R' Q' G' F' A' H' C' P' N' =
      ClosedObservationSupplyBoundaryUp.mk R Q G F A H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hR
  cases hQ
  cases hG
  cases hF
  cases hA
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def closedObservationSupplyBoundaryFields :
    ClosedObservationSupplyBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedObservationSupplyBoundaryUp.mk R Q G F A H C P N => [R, Q, G, F, A, H, C, P, N]

def closedObservationSupplyBoundaryToEventFlow :
    ClosedObservationSupplyBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedObservationSupplyBoundaryUp.mk R Q G F A H C P N =>
      [closedObservationSupplyBoundaryEncodeBHist R,
        closedObservationSupplyBoundaryEncodeBHist Q,
        closedObservationSupplyBoundaryEncodeBHist G,
        closedObservationSupplyBoundaryEncodeBHist F,
        closedObservationSupplyBoundaryEncodeBHist A,
        closedObservationSupplyBoundaryEncodeBHist H,
        closedObservationSupplyBoundaryEncodeBHist C,
        closedObservationSupplyBoundaryEncodeBHist P,
        closedObservationSupplyBoundaryEncodeBHist N]

private def closedObservationSupplyBoundaryEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      closedObservationSupplyBoundaryEventAtDefault index rest

def closedObservationSupplyBoundaryFromEventFlow
    (ef : EventFlow) : Option ClosedObservationSupplyBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ClosedObservationSupplyBoundaryUp.mk
      (closedObservationSupplyBoundaryDecodeBHist
        (closedObservationSupplyBoundaryEventAtDefault 0 ef))
      (closedObservationSupplyBoundaryDecodeBHist
        (closedObservationSupplyBoundaryEventAtDefault 1 ef))
      (closedObservationSupplyBoundaryDecodeBHist
        (closedObservationSupplyBoundaryEventAtDefault 2 ef))
      (closedObservationSupplyBoundaryDecodeBHist
        (closedObservationSupplyBoundaryEventAtDefault 3 ef))
      (closedObservationSupplyBoundaryDecodeBHist
        (closedObservationSupplyBoundaryEventAtDefault 4 ef))
      (closedObservationSupplyBoundaryDecodeBHist
        (closedObservationSupplyBoundaryEventAtDefault 5 ef))
      (closedObservationSupplyBoundaryDecodeBHist
        (closedObservationSupplyBoundaryEventAtDefault 6 ef))
      (closedObservationSupplyBoundaryDecodeBHist
        (closedObservationSupplyBoundaryEventAtDefault 7 ef))
      (closedObservationSupplyBoundaryDecodeBHist
        (closedObservationSupplyBoundaryEventAtDefault 8 ef)))

private theorem closedObservationSupplyBoundary_round_trip :
    ∀ x : ClosedObservationSupplyBoundaryUp,
      closedObservationSupplyBoundaryFromEventFlow
        (closedObservationSupplyBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R Q G F A H C P N =>
      exact
        congrArg some
          (closedObservationSupplyBoundary_mk_congr
            (closedObservationSupplyBoundary_decode_encode_bhist R)
            (closedObservationSupplyBoundary_decode_encode_bhist Q)
            (closedObservationSupplyBoundary_decode_encode_bhist G)
            (closedObservationSupplyBoundary_decode_encode_bhist F)
            (closedObservationSupplyBoundary_decode_encode_bhist A)
            (closedObservationSupplyBoundary_decode_encode_bhist H)
            (closedObservationSupplyBoundary_decode_encode_bhist C)
            (closedObservationSupplyBoundary_decode_encode_bhist P)
            (closedObservationSupplyBoundary_decode_encode_bhist N))

private theorem closedObservationSupplyBoundaryToEventFlow_injective
    {x y : ClosedObservationSupplyBoundaryUp} :
    closedObservationSupplyBoundaryToEventFlow x =
        closedObservationSupplyBoundaryToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedObservationSupplyBoundaryFromEventFlow
          (closedObservationSupplyBoundaryToEventFlow x) =
        closedObservationSupplyBoundaryFromEventFlow
          (closedObservationSupplyBoundaryToEventFlow y) :=
    congrArg closedObservationSupplyBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (closedObservationSupplyBoundary_round_trip x).symm
      (Eq.trans hread (closedObservationSupplyBoundary_round_trip y)))

private theorem closedObservationSupplyBoundary_fields_faithful :
    ∀ x y : ClosedObservationSupplyBoundaryUp,
      closedObservationSupplyBoundaryFields x =
        closedObservationSupplyBoundaryFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R₁ Q₁ G₁ F₁ A₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk R₂ Q₂ G₂ F₂ A₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance closedObservationSupplyBoundaryBHistCarrier :
    BHistCarrier ClosedObservationSupplyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedObservationSupplyBoundaryToEventFlow
  fromEventFlow := closedObservationSupplyBoundaryFromEventFlow

instance closedObservationSupplyBoundaryChapterTasteGate :
    ChapterTasteGate ClosedObservationSupplyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedObservationSupplyBoundaryFromEventFlow
        (closedObservationSupplyBoundaryToEventFlow x) = some x
    exact closedObservationSupplyBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closedObservationSupplyBoundaryToEventFlow_injective heq)

instance closedObservationSupplyBoundaryFieldFaithful :
    FieldFaithful ClosedObservationSupplyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := closedObservationSupplyBoundaryFields
  field_faithful := closedObservationSupplyBoundary_fields_faithful

instance closedObservationSupplyBoundaryNontrivial :
    Nontrivial ClosedObservationSupplyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClosedObservationSupplyBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ClosedObservationSupplyBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ClosedObservationSupplyBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  closedObservationSupplyBoundaryChapterTasteGate

theorem ClosedObservationSupplyBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      closedObservationSupplyBoundaryDecodeBHist
        (closedObservationSupplyBoundaryEncodeBHist h) = h) ∧
      (∀ x : ClosedObservationSupplyBoundaryUp,
        closedObservationSupplyBoundaryFromEventFlow
          (closedObservationSupplyBoundaryToEventFlow x) = some x) ∧
        (∀ x y : ClosedObservationSupplyBoundaryUp,
          closedObservationSupplyBoundaryToEventFlow x =
              closedObservationSupplyBoundaryToEventFlow y →
            x = y) ∧
          closedObservationSupplyBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact closedObservationSupplyBoundary_decode_encode_bhist
  · constructor
    · exact closedObservationSupplyBoundary_round_trip
    · constructor
      · intro x y heq
        exact closedObservationSupplyBoundaryToEventFlow_injective heq
      · rfl

end BEDC.Derived.ClosedObservationSupplyBoundaryUp
