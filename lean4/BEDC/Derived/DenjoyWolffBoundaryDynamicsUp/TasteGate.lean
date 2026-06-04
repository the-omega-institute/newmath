import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DenjoyWolffBoundaryDynamicsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DenjoyWolffBoundaryDynamicsUp : Type where
  | mk
      (diskMap metricRead phaseTransport boundaryRead nonexpansiveRoute fixedBoundary
        transport replay provenance localName : BHist) : DenjoyWolffBoundaryDynamicsUp

def denjoyWolffBoundaryDynamicsEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: denjoyWolffBoundaryDynamicsEncodeBHist h
  | BHist.e1 h => BMark.b1 :: denjoyWolffBoundaryDynamicsEncodeBHist h

def denjoyWolffBoundaryDynamicsDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (denjoyWolffBoundaryDynamicsDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (denjoyWolffBoundaryDynamicsDecodeBHist tail)

private theorem denjoyWolffBoundaryDynamics_decode_encode_bhist :
    ∀ h : BHist,
      denjoyWolffBoundaryDynamicsDecodeBHist
        (denjoyWolffBoundaryDynamicsEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def denjoyWolffBoundaryDynamicsFields :
    DenjoyWolffBoundaryDynamicsUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DenjoyWolffBoundaryDynamicsUp.mk diskMap metricRead phaseTransport boundaryRead
      nonexpansiveRoute fixedBoundary transport replay provenance localName =>
      [diskMap, metricRead, phaseTransport, boundaryRead, nonexpansiveRoute,
        fixedBoundary, transport, replay, provenance, localName]

def denjoyWolffBoundaryDynamicsToEventFlow :
    DenjoyWolffBoundaryDynamicsUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (denjoyWolffBoundaryDynamicsFields x).map denjoyWolffBoundaryDynamicsEncodeBHist

private def denjoyWolffBoundaryDynamicsEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      denjoyWolffBoundaryDynamicsEventAtDefault index rest

def denjoyWolffBoundaryDynamicsFromEventFlow
    (ef : EventFlow) : Option DenjoyWolffBoundaryDynamicsUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DenjoyWolffBoundaryDynamicsUp.mk
      (denjoyWolffBoundaryDynamicsDecodeBHist
        (denjoyWolffBoundaryDynamicsEventAtDefault 0 ef))
      (denjoyWolffBoundaryDynamicsDecodeBHist
        (denjoyWolffBoundaryDynamicsEventAtDefault 1 ef))
      (denjoyWolffBoundaryDynamicsDecodeBHist
        (denjoyWolffBoundaryDynamicsEventAtDefault 2 ef))
      (denjoyWolffBoundaryDynamicsDecodeBHist
        (denjoyWolffBoundaryDynamicsEventAtDefault 3 ef))
      (denjoyWolffBoundaryDynamicsDecodeBHist
        (denjoyWolffBoundaryDynamicsEventAtDefault 4 ef))
      (denjoyWolffBoundaryDynamicsDecodeBHist
        (denjoyWolffBoundaryDynamicsEventAtDefault 5 ef))
      (denjoyWolffBoundaryDynamicsDecodeBHist
        (denjoyWolffBoundaryDynamicsEventAtDefault 6 ef))
      (denjoyWolffBoundaryDynamicsDecodeBHist
        (denjoyWolffBoundaryDynamicsEventAtDefault 7 ef))
      (denjoyWolffBoundaryDynamicsDecodeBHist
        (denjoyWolffBoundaryDynamicsEventAtDefault 8 ef))
      (denjoyWolffBoundaryDynamicsDecodeBHist
        (denjoyWolffBoundaryDynamicsEventAtDefault 9 ef)))

private theorem denjoyWolffBoundaryDynamics_round_trip
    (x : DenjoyWolffBoundaryDynamicsUp) :
    denjoyWolffBoundaryDynamicsFromEventFlow
      (denjoyWolffBoundaryDynamicsToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk diskMap metricRead phaseTransport boundaryRead nonexpansiveRoute fixedBoundary
      transport replay provenance localName =>
      change
        some
          (DenjoyWolffBoundaryDynamicsUp.mk
            (denjoyWolffBoundaryDynamicsDecodeBHist
              (denjoyWolffBoundaryDynamicsEncodeBHist diskMap))
            (denjoyWolffBoundaryDynamicsDecodeBHist
              (denjoyWolffBoundaryDynamicsEncodeBHist metricRead))
            (denjoyWolffBoundaryDynamicsDecodeBHist
              (denjoyWolffBoundaryDynamicsEncodeBHist phaseTransport))
            (denjoyWolffBoundaryDynamicsDecodeBHist
              (denjoyWolffBoundaryDynamicsEncodeBHist boundaryRead))
            (denjoyWolffBoundaryDynamicsDecodeBHist
              (denjoyWolffBoundaryDynamicsEncodeBHist nonexpansiveRoute))
            (denjoyWolffBoundaryDynamicsDecodeBHist
              (denjoyWolffBoundaryDynamicsEncodeBHist fixedBoundary))
            (denjoyWolffBoundaryDynamicsDecodeBHist
              (denjoyWolffBoundaryDynamicsEncodeBHist transport))
            (denjoyWolffBoundaryDynamicsDecodeBHist
              (denjoyWolffBoundaryDynamicsEncodeBHist replay))
            (denjoyWolffBoundaryDynamicsDecodeBHist
              (denjoyWolffBoundaryDynamicsEncodeBHist provenance))
            (denjoyWolffBoundaryDynamicsDecodeBHist
              (denjoyWolffBoundaryDynamicsEncodeBHist localName))) =
          some
            (DenjoyWolffBoundaryDynamicsUp.mk diskMap metricRead phaseTransport
              boundaryRead nonexpansiveRoute fixedBoundary transport replay
              provenance localName)
      rw [denjoyWolffBoundaryDynamics_decode_encode_bhist diskMap,
        denjoyWolffBoundaryDynamics_decode_encode_bhist metricRead,
        denjoyWolffBoundaryDynamics_decode_encode_bhist phaseTransport,
        denjoyWolffBoundaryDynamics_decode_encode_bhist boundaryRead,
        denjoyWolffBoundaryDynamics_decode_encode_bhist nonexpansiveRoute,
        denjoyWolffBoundaryDynamics_decode_encode_bhist fixedBoundary,
        denjoyWolffBoundaryDynamics_decode_encode_bhist transport,
        denjoyWolffBoundaryDynamics_decode_encode_bhist replay,
        denjoyWolffBoundaryDynamics_decode_encode_bhist provenance,
        denjoyWolffBoundaryDynamics_decode_encode_bhist localName]

private theorem denjoyWolffBoundaryDynamicsToEventFlow_injective
    {x y : DenjoyWolffBoundaryDynamicsUp} :
    denjoyWolffBoundaryDynamicsToEventFlow x =
      denjoyWolffBoundaryDynamicsToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      denjoyWolffBoundaryDynamicsFromEventFlow
          (denjoyWolffBoundaryDynamicsToEventFlow x) =
        denjoyWolffBoundaryDynamicsFromEventFlow
          (denjoyWolffBoundaryDynamicsToEventFlow y) :=
    congrArg denjoyWolffBoundaryDynamicsFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (denjoyWolffBoundaryDynamics_round_trip x).symm
      (Eq.trans hread (denjoyWolffBoundaryDynamics_round_trip y)))

private theorem denjoyWolffBoundaryDynamics_field_faithful :
    ∀ x y : DenjoyWolffBoundaryDynamicsUp,
      denjoyWolffBoundaryDynamicsFields x = denjoyWolffBoundaryDynamicsFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk d1 m1 t1 b1 r1 f1 h1 c1 p1 n1 =>
      cases y with
      | mk d2 m2 t2 b2 r2 f2 h2 c2 p2 n2 =>
          cases hfields
          rfl

instance denjoyWolffBoundaryDynamicsBHistCarrier :
    BHistCarrier DenjoyWolffBoundaryDynamicsUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := denjoyWolffBoundaryDynamicsToEventFlow
  fromEventFlow := denjoyWolffBoundaryDynamicsFromEventFlow

instance denjoyWolffBoundaryDynamicsChapterTasteGate :
    ChapterTasteGate DenjoyWolffBoundaryDynamicsUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      denjoyWolffBoundaryDynamicsFromEventFlow
        (denjoyWolffBoundaryDynamicsToEventFlow x) = some x
    exact denjoyWolffBoundaryDynamics_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (denjoyWolffBoundaryDynamicsToEventFlow_injective heq)

instance denjoyWolffBoundaryDynamicsFieldFaithful :
    FieldFaithful DenjoyWolffBoundaryDynamicsUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := denjoyWolffBoundaryDynamicsFields
  field_faithful := denjoyWolffBoundaryDynamics_field_faithful

instance denjoyWolffBoundaryDynamicsNontrivial :
    Nontrivial DenjoyWolffBoundaryDynamicsUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DenjoyWolffBoundaryDynamicsUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      DenjoyWolffBoundaryDynamicsUp.mk (BHist.e1 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DenjoyWolffBoundaryDynamicsUp :=
  -- BEDC touchpoint anchor: BHist BMark
  denjoyWolffBoundaryDynamicsChapterTasteGate

theorem DenjoyWolffBoundaryDynamicsTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      denjoyWolffBoundaryDynamicsDecodeBHist
        (denjoyWolffBoundaryDynamicsEncodeBHist h) = h) ∧
      (∀ x : DenjoyWolffBoundaryDynamicsUp,
        denjoyWolffBoundaryDynamicsFromEventFlow
          (denjoyWolffBoundaryDynamicsToEventFlow x) = some x) ∧
        (∀ x y : DenjoyWolffBoundaryDynamicsUp,
          denjoyWolffBoundaryDynamicsToEventFlow x =
            denjoyWolffBoundaryDynamicsToEventFlow y → x = y) ∧
          denjoyWolffBoundaryDynamicsEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨denjoyWolffBoundaryDynamics_decode_encode_bhist,
      denjoyWolffBoundaryDynamics_round_trip,
      by
        intro x y heq
        exact denjoyWolffBoundaryDynamicsToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.DenjoyWolffBoundaryDynamicsUp
