import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricCompletionAdjointUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricCompletionAdjointUp : Type where
  | mk (M U X F R E H C P N : BHist) : MetricCompletionAdjointUp
  deriving DecidableEq

def metricCompletionAdjointEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricCompletionAdjointEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricCompletionAdjointEncodeBHist h

def metricCompletionAdjointDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricCompletionAdjointDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricCompletionAdjointDecodeBHist tail)

private theorem MetricCompletionAdjointTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      metricCompletionAdjointDecodeBHist (metricCompletionAdjointEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricCompletionAdjointToEventFlow : MetricCompletionAdjointUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetricCompletionAdjointUp.mk M U X F R E H C P N =>
      [[BMark.b0],
        metricCompletionAdjointEncodeBHist M,
        [BMark.b1, BMark.b0],
        metricCompletionAdjointEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b0],
        metricCompletionAdjointEncodeBHist X,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metricCompletionAdjointEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metricCompletionAdjointEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metricCompletionAdjointEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metricCompletionAdjointEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metricCompletionAdjointEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metricCompletionAdjointEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        metricCompletionAdjointEncodeBHist N]

def metricCompletionAdjointFromEventFlow : EventFlow -> Option MetricCompletionAdjointUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tagM :: restM =>
      match restM with
      | [] => none
      | M :: restUTag =>
          match restUTag with
          | [] => none
          | _tagU :: restU =>
              match restU with
              | [] => none
              | U :: restXTag =>
                  match restXTag with
                  | [] => none
                  | _tagX :: restX =>
                      match restX with
                      | [] => none
                      | X :: restFTag =>
                          match restFTag with
                          | [] => none
                          | _tagF :: restF =>
                              match restF with
                              | [] => none
                              | F :: restRTag =>
                                  match restRTag with
                                  | [] => none
                                  | _tagR :: restR =>
                                      match restR with
                                      | [] => none
                                      | R :: restETag =>
                                          match restETag with
                                          | [] => none
                                          | _tagE :: restE =>
                                              match restE with
                                              | [] => none
                                              | E :: restHTag =>
                                                  match restHTag with
                                                  | [] => none
                                                  | _tagH :: restH =>
                                                      match restH with
                                                      | [] => none
                                                      | H :: restCTag =>
                                                          match restCTag with
                                                          | [] => none
                                                          | _tagC :: restC =>
                                                              match restC with
                                                              | [] => none
                                                              | C :: restPTag =>
                                                                  match restPTag with
                                                                  | [] => none
                                                                  | _tagP :: restP =>
                                                                      match restP with
                                                                      | [] => none
                                                                      | P :: restNTag =>
                                                                          match restNTag with
                                                                          | [] => none
                                                                          | _tagN :: restN =>
                                                                              match restN with
                                                                              | [] => none
                                                                              | N :: rest =>
                                                                                  match rest with
                                                                                  | [] =>
                                                                                      some
                                                                                        (MetricCompletionAdjointUp.mk
                                                                                          (metricCompletionAdjointDecodeBHist M)
                                                                                          (metricCompletionAdjointDecodeBHist U)
                                                                                          (metricCompletionAdjointDecodeBHist X)
                                                                                          (metricCompletionAdjointDecodeBHist F)
                                                                                          (metricCompletionAdjointDecodeBHist R)
                                                                                          (metricCompletionAdjointDecodeBHist E)
                                                                                          (metricCompletionAdjointDecodeBHist H)
                                                                                          (metricCompletionAdjointDecodeBHist C)
                                                                                          (metricCompletionAdjointDecodeBHist P)
                                                                                          (metricCompletionAdjointDecodeBHist N))
                                                                                  | _ :: _ => none

private theorem MetricCompletionAdjointTasteGate_single_carrier_alignment_round_trip :
    forall x : MetricCompletionAdjointUp,
      metricCompletionAdjointFromEventFlow (metricCompletionAdjointToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M U X F R E H C P N =>
      change
        some
          (MetricCompletionAdjointUp.mk
            (metricCompletionAdjointDecodeBHist (metricCompletionAdjointEncodeBHist M))
            (metricCompletionAdjointDecodeBHist (metricCompletionAdjointEncodeBHist U))
            (metricCompletionAdjointDecodeBHist (metricCompletionAdjointEncodeBHist X))
            (metricCompletionAdjointDecodeBHist (metricCompletionAdjointEncodeBHist F))
            (metricCompletionAdjointDecodeBHist (metricCompletionAdjointEncodeBHist R))
            (metricCompletionAdjointDecodeBHist (metricCompletionAdjointEncodeBHist E))
            (metricCompletionAdjointDecodeBHist (metricCompletionAdjointEncodeBHist H))
            (metricCompletionAdjointDecodeBHist (metricCompletionAdjointEncodeBHist C))
            (metricCompletionAdjointDecodeBHist (metricCompletionAdjointEncodeBHist P))
            (metricCompletionAdjointDecodeBHist (metricCompletionAdjointEncodeBHist N))) =
          some (MetricCompletionAdjointUp.mk M U X F R E H C P N)
      rw [MetricCompletionAdjointTasteGate_single_carrier_alignment_decode M,
        MetricCompletionAdjointTasteGate_single_carrier_alignment_decode U,
        MetricCompletionAdjointTasteGate_single_carrier_alignment_decode X,
        MetricCompletionAdjointTasteGate_single_carrier_alignment_decode F,
        MetricCompletionAdjointTasteGate_single_carrier_alignment_decode R,
        MetricCompletionAdjointTasteGate_single_carrier_alignment_decode E,
        MetricCompletionAdjointTasteGate_single_carrier_alignment_decode H,
        MetricCompletionAdjointTasteGate_single_carrier_alignment_decode C,
        MetricCompletionAdjointTasteGate_single_carrier_alignment_decode P,
        MetricCompletionAdjointTasteGate_single_carrier_alignment_decode N]

private theorem MetricCompletionAdjointTasteGate_single_carrier_alignment_injective
    {x y : MetricCompletionAdjointUp} :
    metricCompletionAdjointToEventFlow x = metricCompletionAdjointToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricCompletionAdjointFromEventFlow (metricCompletionAdjointToEventFlow x) =
        metricCompletionAdjointFromEventFlow (metricCompletionAdjointToEventFlow y) :=
    congrArg metricCompletionAdjointFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MetricCompletionAdjointTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetricCompletionAdjointTasteGate_single_carrier_alignment_round_trip y)))

private def metricCompletionAdjointFields : MetricCompletionAdjointUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricCompletionAdjointUp.mk M U X F R E H C P N => [M, U, X, F, R, E, H, C, P, N]

private theorem MetricCompletionAdjointTasteGate_single_carrier_alignment_fields :
    forall x y : MetricCompletionAdjointUp,
      metricCompletionAdjointFields x = metricCompletionAdjointFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 U1 X1 F1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 U2 X2 F2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance metricCompletionAdjointBHistCarrier : BHistCarrier MetricCompletionAdjointUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricCompletionAdjointToEventFlow
  fromEventFlow := metricCompletionAdjointFromEventFlow

instance metricCompletionAdjointChapterTasteGate : ChapterTasteGate MetricCompletionAdjointUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metricCompletionAdjointFromEventFlow (metricCompletionAdjointToEventFlow x) = some x
    exact MetricCompletionAdjointTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MetricCompletionAdjointTasteGate_single_carrier_alignment_injective heq)

instance metricCompletionAdjointFieldFaithful : FieldFaithful MetricCompletionAdjointUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metricCompletionAdjointFields
  field_faithful := MetricCompletionAdjointTasteGate_single_carrier_alignment_fields

instance metricCompletionAdjointNontrivial : Nontrivial MetricCompletionAdjointUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetricCompletionAdjointUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetricCompletionAdjointUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem MetricCompletionAdjointTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate MetricCompletionAdjointUp) ∧
      Nonempty (FieldFaithful MetricCompletionAdjointUp) ∧
      Nonempty (Nontrivial MetricCompletionAdjointUp) ∧
      (∀ h : BHist, metricCompletionAdjointDecodeBHist (metricCompletionAdjointEncodeBHist h) = h) ∧
      (∀ x : MetricCompletionAdjointUp,
        metricCompletionAdjointFromEventFlow (metricCompletionAdjointToEventFlow x) = some x) ∧
      (∀ x y : MetricCompletionAdjointUp,
        metricCompletionAdjointToEventFlow x = metricCompletionAdjointToEventFlow y → x = y) ∧
      metricCompletionAdjointEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact ⟨metricCompletionAdjointChapterTasteGate⟩
  constructor
  · exact ⟨metricCompletionAdjointFieldFaithful⟩
  constructor
  · exact ⟨metricCompletionAdjointNontrivial⟩
  constructor
  · exact MetricCompletionAdjointTasteGate_single_carrier_alignment_decode
  constructor
  · exact MetricCompletionAdjointTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact MetricCompletionAdjointTasteGate_single_carrier_alignment_injective heq
  · rfl

end BEDC.Derived.MetricCompletionAdjointUp.TasteGate
