import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicCompletionUp : Type where
  | mk (D W R S L T C P E B : BHist) : DyadicCompletionUp
  deriving DecidableEq

def dyadicCompletionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicCompletionEncodeBHist h

def dyadicCompletionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicCompletionDecodeBHist tail)

private theorem DyadicCompletionTasteGate_single_carrier_alignment_decode :
    forall h : BHist, dyadicCompletionDecodeBHist (dyadicCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicCompletionFields : DyadicCompletionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicCompletionUp.mk D W R S L T C P E B => [D, W, R, S, L, T, C, P, E, B]

def dyadicCompletionToEventFlow : DyadicCompletionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicCompletionFields x).map dyadicCompletionEncodeBHist

def dyadicCompletionFromEventFlow : EventFlow -> Option DyadicCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | D :: rest0 =>
      match rest0 with
      | [] => none
      | W :: rest1 =>
          match rest1 with
          | [] => none
          | R :: rest2 =>
              match rest2 with
              | [] => none
              | S :: rest3 =>
                  match rest3 with
                  | [] => none
                  | L :: rest4 =>
                      match rest4 with
                      | [] => none
                      | T :: rest5 =>
                          match rest5 with
                          | [] => none
                          | C :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | E :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | B :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (DyadicCompletionUp.mk
                                                  (dyadicCompletionDecodeBHist D)
                                                  (dyadicCompletionDecodeBHist W)
                                                  (dyadicCompletionDecodeBHist R)
                                                  (dyadicCompletionDecodeBHist S)
                                                  (dyadicCompletionDecodeBHist L)
                                                  (dyadicCompletionDecodeBHist T)
                                                  (dyadicCompletionDecodeBHist C)
                                                  (dyadicCompletionDecodeBHist P)
                                                  (dyadicCompletionDecodeBHist E)
                                                  (dyadicCompletionDecodeBHist B))
                                          | _ :: _ => none

private theorem DyadicCompletionTasteGate_single_carrier_alignment_round_trip :
    forall x : DyadicCompletionUp,
      dyadicCompletionFromEventFlow (dyadicCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D W R S L T C P E B =>
      change
        some
          (DyadicCompletionUp.mk
            (dyadicCompletionDecodeBHist (dyadicCompletionEncodeBHist D))
            (dyadicCompletionDecodeBHist (dyadicCompletionEncodeBHist W))
            (dyadicCompletionDecodeBHist (dyadicCompletionEncodeBHist R))
            (dyadicCompletionDecodeBHist (dyadicCompletionEncodeBHist S))
            (dyadicCompletionDecodeBHist (dyadicCompletionEncodeBHist L))
            (dyadicCompletionDecodeBHist (dyadicCompletionEncodeBHist T))
            (dyadicCompletionDecodeBHist (dyadicCompletionEncodeBHist C))
            (dyadicCompletionDecodeBHist (dyadicCompletionEncodeBHist P))
            (dyadicCompletionDecodeBHist (dyadicCompletionEncodeBHist E))
            (dyadicCompletionDecodeBHist (dyadicCompletionEncodeBHist B))) =
          some (DyadicCompletionUp.mk D W R S L T C P E B)
      rw [DyadicCompletionTasteGate_single_carrier_alignment_decode D,
        DyadicCompletionTasteGate_single_carrier_alignment_decode W,
        DyadicCompletionTasteGate_single_carrier_alignment_decode R,
        DyadicCompletionTasteGate_single_carrier_alignment_decode S,
        DyadicCompletionTasteGate_single_carrier_alignment_decode L,
        DyadicCompletionTasteGate_single_carrier_alignment_decode T,
        DyadicCompletionTasteGate_single_carrier_alignment_decode C,
        DyadicCompletionTasteGate_single_carrier_alignment_decode P,
        DyadicCompletionTasteGate_single_carrier_alignment_decode E,
        DyadicCompletionTasteGate_single_carrier_alignment_decode B]

private theorem DyadicCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicCompletionUp} :
    dyadicCompletionToEventFlow x = dyadicCompletionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicCompletionFromEventFlow (dyadicCompletionToEventFlow x) =
        dyadicCompletionFromEventFlow (dyadicCompletionToEventFlow y) :=
    congrArg dyadicCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DyadicCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DyadicCompletionTasteGate_single_carrier_alignment_round_trip y)))

private theorem DyadicCompletionTasteGate_single_carrier_alignment_fields :
    forall x y : DyadicCompletionUp, dyadicCompletionFields x = dyadicCompletionFields y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D1 W1 R1 S1 L1 T1 C1 P1 E1 B1 =>
      cases y with
      | mk D2 W2 R2 S2 L2 T2 C2 P2 E2 B2 =>
          cases hfields
          rfl

instance dyadicCompletionBHistCarrier : BHistCarrier DyadicCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicCompletionToEventFlow
  fromEventFlow := dyadicCompletionFromEventFlow

instance dyadicCompletionChapterTasteGate : ChapterTasteGate DyadicCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicCompletionFromEventFlow (dyadicCompletionToEventFlow x) = some x
    exact DyadicCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance dyadicCompletionFieldFaithful : FieldFaithful DyadicCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicCompletionFields
  field_faithful := DyadicCompletionTasteGate_single_carrier_alignment_fields

instance dyadicCompletionNontrivial : BEDC.Meta.TasteGate.Nontrivial DyadicCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DyadicCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DyadicCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicCompletionChapterTasteGate

namespace TasteGate

theorem DyadicCompletionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DyadicCompletionUp) ∧
      Nonempty (FieldFaithful DyadicCompletionUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial DyadicCompletionUp) ∧
          (∀ h : BHist, dyadicCompletionDecodeBHist (dyadicCompletionEncodeBHist h) = h) ∧
            (∀ x : DyadicCompletionUp,
              dyadicCompletionFromEventFlow (dyadicCompletionToEventFlow x) = some x) ∧
              (∀ x y : DyadicCompletionUp,
                dyadicCompletionToEventFlow x = dyadicCompletionToEventFlow y -> x = y) ∧
                dyadicCompletionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨dyadicCompletionChapterTasteGate⟩
  · constructor
    · exact ⟨dyadicCompletionFieldFaithful⟩
    · constructor
      · exact ⟨dyadicCompletionNontrivial⟩
      · constructor
        · exact DyadicCompletionTasteGate_single_carrier_alignment_decode
        · constructor
          · exact DyadicCompletionTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact DyadicCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq
            · rfl

def taste_gate : ChapterTasteGate DyadicCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BEDC.Derived.DyadicCompletionUp.taste_gate

end TasteGate

end BEDC.Derived.DyadicCompletionUp
