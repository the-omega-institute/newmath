import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedMetricCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedMetricCompletionUp : Type where
  | mk (X M F D E R S H C P N : BHist) : LocatedMetricCompletionUp
  deriving DecidableEq

def locatedMetricCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedMetricCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedMetricCompletionEncodeBHist h

def locatedMetricCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedMetricCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedMetricCompletionDecodeBHist tail)

private theorem LocatedMetricCompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      locatedMetricCompletionDecodeBHist (locatedMetricCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def locatedMetricCompletionFields : LocatedMetricCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedMetricCompletionUp.mk X M F D E R S H C P N => [X, M, F, D, E, R, S, H, C, P, N]

def locatedMetricCompletionToEventFlow : LocatedMetricCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedMetricCompletionFields x).map locatedMetricCompletionEncodeBHist

def locatedMetricCompletionFromEventFlow : EventFlow → Option LocatedMetricCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | source :: rest0 =>
      match rest0 with
      | [] => none
      | metric :: rest1 =>
          match rest1 with
          | [] => none
          | filterRow :: rest2 =>
              match rest2 with
              | [] => none
              | directed :: rest3 =>
                  match rest3 with
                  | [] => none
                  | embedding :: rest4 =>
                      match rest4 with
                      | [] => none
                      | readback :: rest5 =>
                          match rest5 with
                          | [] => none
                          | separated :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | replay :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | provenance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | nameRow :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (LocatedMetricCompletionUp.mk
                                                      (locatedMetricCompletionDecodeBHist source)
                                                      (locatedMetricCompletionDecodeBHist metric)
                                                      (locatedMetricCompletionDecodeBHist filterRow)
                                                      (locatedMetricCompletionDecodeBHist directed)
                                                      (locatedMetricCompletionDecodeBHist embedding)
                                                      (locatedMetricCompletionDecodeBHist readback)
                                                      (locatedMetricCompletionDecodeBHist separated)
                                                      (locatedMetricCompletionDecodeBHist transport)
                                                      (locatedMetricCompletionDecodeBHist replay)
                                                      (locatedMetricCompletionDecodeBHist provenance)
                                                      (locatedMetricCompletionDecodeBHist nameRow))
                                              | _ :: _ => none

private theorem LocatedMetricCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedMetricCompletionUp,
      locatedMetricCompletionFromEventFlow
        (locatedMetricCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X M F D E R S H C P N =>
      change
        some
          (LocatedMetricCompletionUp.mk
            (locatedMetricCompletionDecodeBHist (locatedMetricCompletionEncodeBHist X))
            (locatedMetricCompletionDecodeBHist (locatedMetricCompletionEncodeBHist M))
            (locatedMetricCompletionDecodeBHist (locatedMetricCompletionEncodeBHist F))
            (locatedMetricCompletionDecodeBHist (locatedMetricCompletionEncodeBHist D))
            (locatedMetricCompletionDecodeBHist (locatedMetricCompletionEncodeBHist E))
            (locatedMetricCompletionDecodeBHist (locatedMetricCompletionEncodeBHist R))
            (locatedMetricCompletionDecodeBHist (locatedMetricCompletionEncodeBHist S))
            (locatedMetricCompletionDecodeBHist (locatedMetricCompletionEncodeBHist H))
            (locatedMetricCompletionDecodeBHist (locatedMetricCompletionEncodeBHist C))
            (locatedMetricCompletionDecodeBHist (locatedMetricCompletionEncodeBHist P))
            (locatedMetricCompletionDecodeBHist (locatedMetricCompletionEncodeBHist N))) =
          some (LocatedMetricCompletionUp.mk X M F D E R S H C P N)
      rw [LocatedMetricCompletionTasteGate_single_carrier_alignment_decode_encode X,
        LocatedMetricCompletionTasteGate_single_carrier_alignment_decode_encode M,
        LocatedMetricCompletionTasteGate_single_carrier_alignment_decode_encode F,
        LocatedMetricCompletionTasteGate_single_carrier_alignment_decode_encode D,
        LocatedMetricCompletionTasteGate_single_carrier_alignment_decode_encode E,
        LocatedMetricCompletionTasteGate_single_carrier_alignment_decode_encode R,
        LocatedMetricCompletionTasteGate_single_carrier_alignment_decode_encode S,
        LocatedMetricCompletionTasteGate_single_carrier_alignment_decode_encode H,
        LocatedMetricCompletionTasteGate_single_carrier_alignment_decode_encode C,
        LocatedMetricCompletionTasteGate_single_carrier_alignment_decode_encode P,
        LocatedMetricCompletionTasteGate_single_carrier_alignment_decode_encode N]

private theorem LocatedMetricCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedMetricCompletionUp} :
    locatedMetricCompletionToEventFlow x = locatedMetricCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedMetricCompletionFromEventFlow (locatedMetricCompletionToEventFlow x) =
        locatedMetricCompletionFromEventFlow (locatedMetricCompletionToEventFlow y) :=
    congrArg locatedMetricCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedMetricCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedMetricCompletionTasteGate_single_carrier_alignment_round_trip y)))

private theorem LocatedMetricCompletionTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : LocatedMetricCompletionUp, locatedMetricCompletionFields x =
      locatedMetricCompletionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ M₁ F₁ D₁ E₁ R₁ S₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ M₂ F₂ D₂ E₂ R₂ S₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hX t0
          injection t0 with hM t1
          injection t1 with hF t2
          injection t2 with hD t3
          injection t3 with hE t4
          injection t4 with hR t5
          injection t5 with hS t6
          injection t6 with hH t7
          injection t7 with hC t8
          injection t8 with hP t9
          injection t9 with hN _
          subst hX
          subst hM
          subst hF
          subst hD
          subst hE
          subst hR
          subst hS
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance locatedMetricCompletionBHistCarrier :
    BHistCarrier LocatedMetricCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedMetricCompletionToEventFlow
  fromEventFlow := locatedMetricCompletionFromEventFlow

instance locatedMetricCompletionChapterTasteGate :
    ChapterTasteGate LocatedMetricCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedMetricCompletionFromEventFlow (locatedMetricCompletionToEventFlow x) = some x
    exact LocatedMetricCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LocatedMetricCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance locatedMetricCompletionFieldFaithful :
    FieldFaithful LocatedMetricCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedMetricCompletionFields
  field_faithful := LocatedMetricCompletionTasteGate_single_carrier_alignment_fields_faithful

instance locatedMetricCompletionNontrivial : Nontrivial LocatedMetricCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedMetricCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedMetricCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocatedMetricCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedMetricCompletionChapterTasteGate

theorem LocatedMetricCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedMetricCompletionDecodeBHist
      (locatedMetricCompletionEncodeBHist h) = h) ∧
      (∀ x : LocatedMetricCompletionUp,
        locatedMetricCompletionFromEventFlow
          (locatedMetricCompletionToEventFlow x) = some x) ∧
        (∀ x y : LocatedMetricCompletionUp,
          locatedMetricCompletionToEventFlow x =
            locatedMetricCompletionToEventFlow y → x = y) ∧
          locatedMetricCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨LocatedMetricCompletionTasteGate_single_carrier_alignment_decode_encode,
      LocatedMetricCompletionTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        LocatedMetricCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.LocatedMetricCompletionUp
