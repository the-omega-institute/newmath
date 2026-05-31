import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompletionPreservesSeparableUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompletionPreservesSeparableUp : Type where
  | mk (M D C W T R I H P N : BHist) : CompletionPreservesSeparableUp
  deriving DecidableEq

def completionPreservesSeparableEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completionPreservesSeparableEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completionPreservesSeparableEncodeBHist h

def completionPreservesSeparableDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completionPreservesSeparableDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completionPreservesSeparableDecodeBHist tail)

private theorem CompletionPreservesSeparableTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      completionPreservesSeparableDecodeBHist
        (completionPreservesSeparableEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def completionPreservesSeparableFields :
    CompletionPreservesSeparableUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompletionPreservesSeparableUp.mk M D C W T R I H P N => [M, D, C, W, T, R, I, H, P, N]

def completionPreservesSeparableToEventFlow :
    CompletionPreservesSeparableUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (completionPreservesSeparableFields x).map completionPreservesSeparableEncodeBHist

def completionPreservesSeparableFromEventFlow :
    EventFlow → Option CompletionPreservesSeparableUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | metric :: rest0 =>
      match rest0 with
      | [] => none
      | dense :: rest1 =>
          match rest1 with
          | [] => none
          | completion :: rest2 =>
              match rest2 with
              | [] => none
              | windows :: rest3 =>
                  match rest3 with
                  | [] => none
                  | tolerance :: rest4 =>
                      match rest4 with
                      | [] => none
                      | readback :: rest5 =>
                          match rest5 with
                          | [] => none
                          | handoff :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | nameRow :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (CompletionPreservesSeparableUp.mk
                                                  (completionPreservesSeparableDecodeBHist metric)
                                                  (completionPreservesSeparableDecodeBHist dense)
                                                  (completionPreservesSeparableDecodeBHist completion)
                                                  (completionPreservesSeparableDecodeBHist windows)
                                                  (completionPreservesSeparableDecodeBHist tolerance)
                                                  (completionPreservesSeparableDecodeBHist readback)
                                                  (completionPreservesSeparableDecodeBHist handoff)
                                                  (completionPreservesSeparableDecodeBHist transport)
                                                  (completionPreservesSeparableDecodeBHist provenance)
                                                  (completionPreservesSeparableDecodeBHist nameRow))
                                          | _ :: _ => none

private theorem CompletionPreservesSeparableTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompletionPreservesSeparableUp,
      completionPreservesSeparableFromEventFlow
        (completionPreservesSeparableToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M D C W T R I H P N =>
      change
        some
          (CompletionPreservesSeparableUp.mk
            (completionPreservesSeparableDecodeBHist
              (completionPreservesSeparableEncodeBHist M))
            (completionPreservesSeparableDecodeBHist
              (completionPreservesSeparableEncodeBHist D))
            (completionPreservesSeparableDecodeBHist
              (completionPreservesSeparableEncodeBHist C))
            (completionPreservesSeparableDecodeBHist
              (completionPreservesSeparableEncodeBHist W))
            (completionPreservesSeparableDecodeBHist
              (completionPreservesSeparableEncodeBHist T))
            (completionPreservesSeparableDecodeBHist
              (completionPreservesSeparableEncodeBHist R))
            (completionPreservesSeparableDecodeBHist
              (completionPreservesSeparableEncodeBHist I))
            (completionPreservesSeparableDecodeBHist
              (completionPreservesSeparableEncodeBHist H))
            (completionPreservesSeparableDecodeBHist
              (completionPreservesSeparableEncodeBHist P))
            (completionPreservesSeparableDecodeBHist
              (completionPreservesSeparableEncodeBHist N))) =
          some (CompletionPreservesSeparableUp.mk M D C W T R I H P N)
      rw [CompletionPreservesSeparableTasteGate_single_carrier_alignment_decode_encode M,
        CompletionPreservesSeparableTasteGate_single_carrier_alignment_decode_encode D,
        CompletionPreservesSeparableTasteGate_single_carrier_alignment_decode_encode C,
        CompletionPreservesSeparableTasteGate_single_carrier_alignment_decode_encode W,
        CompletionPreservesSeparableTasteGate_single_carrier_alignment_decode_encode T,
        CompletionPreservesSeparableTasteGate_single_carrier_alignment_decode_encode R,
        CompletionPreservesSeparableTasteGate_single_carrier_alignment_decode_encode I,
        CompletionPreservesSeparableTasteGate_single_carrier_alignment_decode_encode H,
        CompletionPreservesSeparableTasteGate_single_carrier_alignment_decode_encode P,
        CompletionPreservesSeparableTasteGate_single_carrier_alignment_decode_encode N]

private theorem CompletionPreservesSeparableTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompletionPreservesSeparableUp} :
    completionPreservesSeparableToEventFlow x =
      completionPreservesSeparableToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completionPreservesSeparableFromEventFlow
          (completionPreservesSeparableToEventFlow x) =
        completionPreservesSeparableFromEventFlow
          (completionPreservesSeparableToEventFlow y) :=
    congrArg completionPreservesSeparableFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompletionPreservesSeparableTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompletionPreservesSeparableTasteGate_single_carrier_alignment_round_trip y)))

private theorem CompletionPreservesSeparableTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CompletionPreservesSeparableUp,
      completionPreservesSeparableFields x =
        completionPreservesSeparableFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ D₁ C₁ W₁ T₁ R₁ I₁ H₁ P₁ N₁ =>
      cases y with
      | mk M₂ D₂ C₂ W₂ T₂ R₂ I₂ H₂ P₂ N₂ =>
          injection hfields with hM t0
          injection t0 with hD t1
          injection t1 with hC t2
          injection t2 with hW t3
          injection t3 with hT t4
          injection t4 with hR t5
          injection t5 with hI t6
          injection t6 with hH t7
          injection t7 with hP t8
          injection t8 with hN _
          subst hM
          subst hD
          subst hC
          subst hW
          subst hT
          subst hR
          subst hI
          subst hH
          subst hP
          subst hN
          rfl

instance completionPreservesSeparableBHistCarrier :
    BHistCarrier CompletionPreservesSeparableUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completionPreservesSeparableToEventFlow
  fromEventFlow := completionPreservesSeparableFromEventFlow

instance completionPreservesSeparableChapterTasteGate :
    ChapterTasteGate CompletionPreservesSeparableUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      completionPreservesSeparableFromEventFlow
        (completionPreservesSeparableToEventFlow x) = some x
    exact CompletionPreservesSeparableTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompletionPreservesSeparableTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance completionPreservesSeparableFieldFaithful :
    FieldFaithful CompletionPreservesSeparableUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := completionPreservesSeparableFields
  field_faithful := CompletionPreservesSeparableTasteGate_single_carrier_alignment_fields_faithful

instance completionPreservesSeparableNontrivial :
    Nontrivial CompletionPreservesSeparableUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompletionPreservesSeparableUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompletionPreservesSeparableUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CompletionPreservesSeparableUp :=
  -- BEDC touchpoint anchor: BHist BMark
  completionPreservesSeparableChapterTasteGate

theorem CompletionPreservesSeparableTasteGate_single_carrier_alignment :
    (∀ h : BHist, completionPreservesSeparableDecodeBHist
      (completionPreservesSeparableEncodeBHist h) = h) ∧
      (∀ x : CompletionPreservesSeparableUp,
        completionPreservesSeparableFromEventFlow
          (completionPreservesSeparableToEventFlow x) = some x) ∧
        (∀ x y : CompletionPreservesSeparableUp,
          completionPreservesSeparableToEventFlow x =
            completionPreservesSeparableToEventFlow y → x = y) ∧
          completionPreservesSeparableEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨CompletionPreservesSeparableTasteGate_single_carrier_alignment_decode_encode,
      CompletionPreservesSeparableTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        CompletionPreservesSeparableTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.CompletionPreservesSeparableUp
