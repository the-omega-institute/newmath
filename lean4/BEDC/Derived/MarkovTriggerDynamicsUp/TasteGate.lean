import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MarkovTriggerDynamicsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MarkovTriggerDynamicsUp : Type where
  | mk (S K A D G H C P N : BHist) : MarkovTriggerDynamicsUp
  deriving DecidableEq

def markovTriggerDynamicsEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: markovTriggerDynamicsEncodeBHist h
  | BHist.e1 h => BMark.b1 :: markovTriggerDynamicsEncodeBHist h

def markovTriggerDynamicsDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (markovTriggerDynamicsDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (markovTriggerDynamicsDecodeBHist tail)

private theorem markovTriggerDynamics_decode_encode_bhist :
    forall h : BHist,
      markovTriggerDynamicsDecodeBHist (markovTriggerDynamicsEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def markovTriggerDynamicsFields : MarkovTriggerDynamicsUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MarkovTriggerDynamicsUp.mk S K A D G H C P N =>
      [S, K, A, D, G, H, C, P, N]

def markovTriggerDynamicsToEventFlow : MarkovTriggerDynamicsUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MarkovTriggerDynamicsUp.mk S K A D G H C P N =>
      [markovTriggerDynamicsEncodeBHist S,
        markovTriggerDynamicsEncodeBHist K,
        markovTriggerDynamicsEncodeBHist A,
        markovTriggerDynamicsEncodeBHist D,
        markovTriggerDynamicsEncodeBHist G,
        markovTriggerDynamicsEncodeBHist H,
        markovTriggerDynamicsEncodeBHist C,
        markovTriggerDynamicsEncodeBHist P,
        markovTriggerDynamicsEncodeBHist N]

def markovTriggerDynamicsFromEventFlow :
    EventFlow -> Option MarkovTriggerDynamicsUp
  -- BEDC touchpoint anchor: BHist BMark
  | [S, K, A, D, G, H, C, P, N] =>
      some
        (MarkovTriggerDynamicsUp.mk
          (markovTriggerDynamicsDecodeBHist S)
          (markovTriggerDynamicsDecodeBHist K)
          (markovTriggerDynamicsDecodeBHist A)
          (markovTriggerDynamicsDecodeBHist D)
          (markovTriggerDynamicsDecodeBHist G)
          (markovTriggerDynamicsDecodeBHist H)
          (markovTriggerDynamicsDecodeBHist C)
          (markovTriggerDynamicsDecodeBHist P)
          (markovTriggerDynamicsDecodeBHist N))
  | _ => none

private theorem markovTriggerDynamics_round_trip :
    forall x : MarkovTriggerDynamicsUp,
      markovTriggerDynamicsFromEventFlow (markovTriggerDynamicsToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S K A D G H C P N =>
      change
        some
          (MarkovTriggerDynamicsUp.mk
            (markovTriggerDynamicsDecodeBHist (markovTriggerDynamicsEncodeBHist S))
            (markovTriggerDynamicsDecodeBHist (markovTriggerDynamicsEncodeBHist K))
            (markovTriggerDynamicsDecodeBHist (markovTriggerDynamicsEncodeBHist A))
            (markovTriggerDynamicsDecodeBHist (markovTriggerDynamicsEncodeBHist D))
            (markovTriggerDynamicsDecodeBHist (markovTriggerDynamicsEncodeBHist G))
            (markovTriggerDynamicsDecodeBHist (markovTriggerDynamicsEncodeBHist H))
            (markovTriggerDynamicsDecodeBHist (markovTriggerDynamicsEncodeBHist C))
            (markovTriggerDynamicsDecodeBHist (markovTriggerDynamicsEncodeBHist P))
            (markovTriggerDynamicsDecodeBHist (markovTriggerDynamicsEncodeBHist N))) =
          some (MarkovTriggerDynamicsUp.mk S K A D G H C P N)
      rw [markovTriggerDynamics_decode_encode_bhist S,
        markovTriggerDynamics_decode_encode_bhist K,
        markovTriggerDynamics_decode_encode_bhist A,
        markovTriggerDynamics_decode_encode_bhist D,
        markovTriggerDynamics_decode_encode_bhist G,
        markovTriggerDynamics_decode_encode_bhist H,
        markovTriggerDynamics_decode_encode_bhist C,
        markovTriggerDynamics_decode_encode_bhist P,
        markovTriggerDynamics_decode_encode_bhist N]

private theorem markovTriggerDynamicsToEventFlow_injective
    {x y : MarkovTriggerDynamicsUp} :
    markovTriggerDynamicsToEventFlow x = markovTriggerDynamicsToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      markovTriggerDynamicsFromEventFlow (markovTriggerDynamicsToEventFlow x) =
        markovTriggerDynamicsFromEventFlow (markovTriggerDynamicsToEventFlow y) :=
    congrArg markovTriggerDynamicsFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (markovTriggerDynamics_round_trip x).symm
      (Eq.trans hread (markovTriggerDynamics_round_trip y)))

private theorem markovTriggerDynamics_field_faithful :
    forall x y : MarkovTriggerDynamicsUp,
      markovTriggerDynamicsFields x = markovTriggerDynamicsFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk S1 K1 A1 D1 G1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 K2 A2 D2 G2 H2 C2 P2 N2 =>
          cases h
          rfl

instance markovTriggerDynamicsBHistCarrier :
    BHistCarrier MarkovTriggerDynamicsUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := markovTriggerDynamicsToEventFlow
  fromEventFlow := markovTriggerDynamicsFromEventFlow

instance markovTriggerDynamicsChapterTasteGate :
    ChapterTasteGate MarkovTriggerDynamicsUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change markovTriggerDynamicsFromEventFlow (markovTriggerDynamicsToEventFlow x) = some x
    exact markovTriggerDynamics_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (markovTriggerDynamicsToEventFlow_injective heq)

instance markovTriggerDynamicsFieldFaithful :
    FieldFaithful MarkovTriggerDynamicsUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := markovTriggerDynamicsFields
  field_faithful := markovTriggerDynamics_field_faithful

instance markovTriggerDynamicsNontrivial :
    Nontrivial MarkovTriggerDynamicsUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MarkovTriggerDynamicsUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MarkovTriggerDynamicsUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MarkovTriggerDynamicsUp :=
  -- BEDC touchpoint anchor: BHist BMark
  markovTriggerDynamicsChapterTasteGate

theorem MarkovTriggerDynamicsTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      markovTriggerDynamicsDecodeBHist
        (markovTriggerDynamicsEncodeBHist h) = h) ∧
      (∀ x y : MarkovTriggerDynamicsUp,
        markovTriggerDynamicsFields x =
          markovTriggerDynamicsFields y -> x = y) ∧
        (∃ x y : MarkovTriggerDynamicsUp, x ≠ y) ∧
          markovTriggerDynamicsEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨markovTriggerDynamics_decode_encode_bhist,
      markovTriggerDynamics_field_faithful,
      ⟨MarkovTriggerDynamicsUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        MarkovTriggerDynamicsUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩,
      rfl⟩

end BEDC.Derived.MarkovTriggerDynamicsUp
