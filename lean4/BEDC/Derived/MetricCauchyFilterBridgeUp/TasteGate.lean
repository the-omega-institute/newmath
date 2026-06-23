import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricCauchyFilterBridgeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricCauchyFilterBridgeUp : Type where
  | mk (X F S D R E H C P N : BHist) : MetricCauchyFilterBridgeUp
  deriving DecidableEq

def metricCauchyFilterBridgeEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricCauchyFilterBridgeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricCauchyFilterBridgeEncodeBHist h

def metricCauchyFilterBridgeDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricCauchyFilterBridgeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricCauchyFilterBridgeDecodeBHist tail)

private theorem MetricCauchyFilterBridgeTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      metricCauchyFilterBridgeDecodeBHist
        (metricCauchyFilterBridgeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricCauchyFilterBridgeFields :
    MetricCauchyFilterBridgeUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricCauchyFilterBridgeUp.mk X F S D R E H C P N => [X, F, S, D, R, E, H, C, P, N]

def metricCauchyFilterBridgeToEventFlow :
    MetricCauchyFilterBridgeUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metricCauchyFilterBridgeFields x).map metricCauchyFilterBridgeEncodeBHist

def metricCauchyFilterBridgeFromEventFlow :
    EventFlow -> Option MetricCauchyFilterBridgeUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | X :: rest0 =>
      match rest0 with
      | [] => none
      | F :: rest1 =>
          match rest1 with
          | [] => none
          | S :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | E :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (MetricCauchyFilterBridgeUp.mk
                                                  (metricCauchyFilterBridgeDecodeBHist X)
                                                  (metricCauchyFilterBridgeDecodeBHist F)
                                                  (metricCauchyFilterBridgeDecodeBHist S)
                                                  (metricCauchyFilterBridgeDecodeBHist D)
                                                  (metricCauchyFilterBridgeDecodeBHist R)
                                                  (metricCauchyFilterBridgeDecodeBHist E)
                                                  (metricCauchyFilterBridgeDecodeBHist H)
                                                  (metricCauchyFilterBridgeDecodeBHist C)
                                                  (metricCauchyFilterBridgeDecodeBHist P)
                                                  (metricCauchyFilterBridgeDecodeBHist N))
                                          | _ :: _ => none

private theorem MetricCauchyFilterBridgeTasteGate_single_carrier_alignment_round_trip :
    forall x : MetricCauchyFilterBridgeUp,
      metricCauchyFilterBridgeFromEventFlow
        (metricCauchyFilterBridgeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X F S D R E H C P N =>
      change
        some
          (MetricCauchyFilterBridgeUp.mk
            (metricCauchyFilterBridgeDecodeBHist
              (metricCauchyFilterBridgeEncodeBHist X))
            (metricCauchyFilterBridgeDecodeBHist
              (metricCauchyFilterBridgeEncodeBHist F))
            (metricCauchyFilterBridgeDecodeBHist
              (metricCauchyFilterBridgeEncodeBHist S))
            (metricCauchyFilterBridgeDecodeBHist
              (metricCauchyFilterBridgeEncodeBHist D))
            (metricCauchyFilterBridgeDecodeBHist
              (metricCauchyFilterBridgeEncodeBHist R))
            (metricCauchyFilterBridgeDecodeBHist
              (metricCauchyFilterBridgeEncodeBHist E))
            (metricCauchyFilterBridgeDecodeBHist
              (metricCauchyFilterBridgeEncodeBHist H))
            (metricCauchyFilterBridgeDecodeBHist
              (metricCauchyFilterBridgeEncodeBHist C))
            (metricCauchyFilterBridgeDecodeBHist
              (metricCauchyFilterBridgeEncodeBHist P))
            (metricCauchyFilterBridgeDecodeBHist
              (metricCauchyFilterBridgeEncodeBHist N))) =
          some (MetricCauchyFilterBridgeUp.mk X F S D R E H C P N)
      rw [MetricCauchyFilterBridgeTasteGate_single_carrier_alignment_decode X,
        MetricCauchyFilterBridgeTasteGate_single_carrier_alignment_decode F,
        MetricCauchyFilterBridgeTasteGate_single_carrier_alignment_decode S,
        MetricCauchyFilterBridgeTasteGate_single_carrier_alignment_decode D,
        MetricCauchyFilterBridgeTasteGate_single_carrier_alignment_decode R,
        MetricCauchyFilterBridgeTasteGate_single_carrier_alignment_decode E,
        MetricCauchyFilterBridgeTasteGate_single_carrier_alignment_decode H,
        MetricCauchyFilterBridgeTasteGate_single_carrier_alignment_decode C,
        MetricCauchyFilterBridgeTasteGate_single_carrier_alignment_decode P,
        MetricCauchyFilterBridgeTasteGate_single_carrier_alignment_decode N]

private theorem MetricCauchyFilterBridgeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MetricCauchyFilterBridgeUp} :
    metricCauchyFilterBridgeToEventFlow x =
      metricCauchyFilterBridgeToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricCauchyFilterBridgeFromEventFlow
          (metricCauchyFilterBridgeToEventFlow x) =
        metricCauchyFilterBridgeFromEventFlow
          (metricCauchyFilterBridgeToEventFlow y) :=
    congrArg metricCauchyFilterBridgeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MetricCauchyFilterBridgeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetricCauchyFilterBridgeTasteGate_single_carrier_alignment_round_trip y)))

private theorem MetricCauchyFilterBridgeTasteGate_single_carrier_alignment_fields :
    forall x y : MetricCauchyFilterBridgeUp,
      metricCauchyFilterBridgeFields x =
        metricCauchyFilterBridgeFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 F1 S1 D1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 F2 S2 D2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance metricCauchyFilterBridgeBHistCarrier :
    BHistCarrier MetricCauchyFilterBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricCauchyFilterBridgeToEventFlow
  fromEventFlow := metricCauchyFilterBridgeFromEventFlow

instance metricCauchyFilterBridgeChapterTasteGate :
    ChapterTasteGate MetricCauchyFilterBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metricCauchyFilterBridgeFromEventFlow
        (metricCauchyFilterBridgeToEventFlow x) = some x
    exact MetricCauchyFilterBridgeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MetricCauchyFilterBridgeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance metricCauchyFilterBridgeFieldFaithful :
    FieldFaithful MetricCauchyFilterBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metricCauchyFilterBridgeFields
  field_faithful := MetricCauchyFilterBridgeTasteGate_single_carrier_alignment_fields

instance metricCauchyFilterBridgeNontrivial :
    Nontrivial MetricCauchyFilterBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetricCauchyFilterBridgeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetricCauchyFilterBridgeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetricCauchyFilterBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricCauchyFilterBridgeChapterTasteGate

theorem MetricCauchyFilterBridgeTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate MetricCauchyFilterBridgeUp) ∧
      Nonempty (FieldFaithful MetricCauchyFilterBridgeUp) ∧
        Nonempty (Nontrivial MetricCauchyFilterBridgeUp) ∧
          (∀ x : MetricCauchyFilterBridgeUp,
            metricCauchyFilterBridgeFromEventFlow
              (metricCauchyFilterBridgeToEventFlow x) = some x) ∧
            (∀ x y : MetricCauchyFilterBridgeUp,
              metricCauchyFilterBridgeToEventFlow x =
                metricCauchyFilterBridgeToEventFlow y -> x = y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨metricCauchyFilterBridgeChapterTasteGate⟩
  · constructor
    · exact ⟨metricCauchyFilterBridgeFieldFaithful⟩
    · constructor
      · exact ⟨metricCauchyFilterBridgeNontrivial⟩
      · constructor
        · exact MetricCauchyFilterBridgeTasteGate_single_carrier_alignment_round_trip
        · intro x y heq
          exact
            MetricCauchyFilterBridgeTasteGate_single_carrier_alignment_toEventFlow_injective
              heq

end BEDC.Derived.MetricCauchyFilterBridgeUp
