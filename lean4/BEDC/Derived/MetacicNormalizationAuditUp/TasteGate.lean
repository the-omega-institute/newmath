import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetacicNormalizationAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetacicNormalizationAuditUp : Type where
  | mk : (R C S A N F H T P L : BHist) -> MetacicNormalizationAuditUp
  deriving DecidableEq

def metacicNormalizationAuditEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metacicNormalizationAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metacicNormalizationAuditEncodeBHist h

def metacicNormalizationAuditDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metacicNormalizationAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metacicNormalizationAuditDecodeBHist tail)

theorem MetacicNormalizationAuditTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      metacicNormalizationAuditDecodeBHist (metacicNormalizationAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metacicNormalizationAuditFields : MetacicNormalizationAuditUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetacicNormalizationAuditUp.mk R C S A N F H T P L => [R, C, S, A, N, F, H, T, P, L]

def metacicNormalizationAuditToEventFlow : MetacicNormalizationAuditUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metacicNormalizationAuditFields x).map metacicNormalizationAuditEncodeBHist

def metacicNormalizationAuditFromEventFlow : EventFlow -> Option MetacicNormalizationAuditUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | R :: rest0 =>
      match rest0 with
      | [] => none
      | C :: rest1 =>
          match rest1 with
          | [] => none
          | S :: rest2 =>
              match rest2 with
              | [] => none
              | A :: rest3 =>
                  match rest3 with
                  | [] => none
                  | N :: rest4 =>
                      match rest4 with
                      | [] => none
                      | F :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | T :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | L :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (MetacicNormalizationAuditUp.mk
                                                  (metacicNormalizationAuditDecodeBHist R)
                                                  (metacicNormalizationAuditDecodeBHist C)
                                                  (metacicNormalizationAuditDecodeBHist S)
                                                  (metacicNormalizationAuditDecodeBHist A)
                                                  (metacicNormalizationAuditDecodeBHist N)
                                                  (metacicNormalizationAuditDecodeBHist F)
                                                  (metacicNormalizationAuditDecodeBHist H)
                                                  (metacicNormalizationAuditDecodeBHist T)
                                                  (metacicNormalizationAuditDecodeBHist P)
                                                  (metacicNormalizationAuditDecodeBHist L))
                                          | _ :: _ => none

theorem MetacicNormalizationAuditTasteGate_single_carrier_alignment_round_trip :
    forall x : MetacicNormalizationAuditUp,
      metacicNormalizationAuditFromEventFlow
        (metacicNormalizationAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R C S A N F H T P L =>
      change
        some
          (MetacicNormalizationAuditUp.mk
            (metacicNormalizationAuditDecodeBHist (metacicNormalizationAuditEncodeBHist R))
            (metacicNormalizationAuditDecodeBHist (metacicNormalizationAuditEncodeBHist C))
            (metacicNormalizationAuditDecodeBHist (metacicNormalizationAuditEncodeBHist S))
            (metacicNormalizationAuditDecodeBHist (metacicNormalizationAuditEncodeBHist A))
            (metacicNormalizationAuditDecodeBHist (metacicNormalizationAuditEncodeBHist N))
            (metacicNormalizationAuditDecodeBHist (metacicNormalizationAuditEncodeBHist F))
            (metacicNormalizationAuditDecodeBHist (metacicNormalizationAuditEncodeBHist H))
            (metacicNormalizationAuditDecodeBHist (metacicNormalizationAuditEncodeBHist T))
            (metacicNormalizationAuditDecodeBHist (metacicNormalizationAuditEncodeBHist P))
            (metacicNormalizationAuditDecodeBHist (metacicNormalizationAuditEncodeBHist L))) =
          some (MetacicNormalizationAuditUp.mk R C S A N F H T P L)
      rw [MetacicNormalizationAuditTasteGate_single_carrier_alignment_decode_encode R,
        MetacicNormalizationAuditTasteGate_single_carrier_alignment_decode_encode C,
        MetacicNormalizationAuditTasteGate_single_carrier_alignment_decode_encode S,
        MetacicNormalizationAuditTasteGate_single_carrier_alignment_decode_encode A,
        MetacicNormalizationAuditTasteGate_single_carrier_alignment_decode_encode N,
        MetacicNormalizationAuditTasteGate_single_carrier_alignment_decode_encode F,
        MetacicNormalizationAuditTasteGate_single_carrier_alignment_decode_encode H,
        MetacicNormalizationAuditTasteGate_single_carrier_alignment_decode_encode T,
        MetacicNormalizationAuditTasteGate_single_carrier_alignment_decode_encode P,
        MetacicNormalizationAuditTasteGate_single_carrier_alignment_decode_encode L]

theorem MetacicNormalizationAuditTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MetacicNormalizationAuditUp} :
    metacicNormalizationAuditToEventFlow x = metacicNormalizationAuditToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metacicNormalizationAuditFromEventFlow (metacicNormalizationAuditToEventFlow x) =
        metacicNormalizationAuditFromEventFlow (metacicNormalizationAuditToEventFlow y) :=
    congrArg metacicNormalizationAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MetacicNormalizationAuditTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetacicNormalizationAuditTasteGate_single_carrier_alignment_round_trip y)))

theorem MetacicNormalizationAuditTasteGate_single_carrier_alignment_field_faithful :
    forall x y : MetacicNormalizationAuditUp,
      metacicNormalizationAuditFields x = metacicNormalizationAuditFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R₁ C₁ S₁ A₁ N₁ F₁ H₁ T₁ P₁ L₁ =>
      cases y with
      | mk R₂ C₂ S₂ A₂ N₂ F₂ H₂ T₂ P₂ L₂ =>
          cases hfields
          rfl

instance metacicNormalizationAuditBHistCarrier :
    BHistCarrier MetacicNormalizationAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metacicNormalizationAuditToEventFlow
  fromEventFlow := metacicNormalizationAuditFromEventFlow

instance metacicNormalizationAuditChapterTasteGate :
    ChapterTasteGate MetacicNormalizationAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x =>
    id (MetacicNormalizationAuditTasteGate_single_carrier_alignment_round_trip x)
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MetacicNormalizationAuditTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance metacicNormalizationAuditFieldFaithful :
    FieldFaithful MetacicNormalizationAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metacicNormalizationAuditFields
  field_faithful := MetacicNormalizationAuditTasteGate_single_carrier_alignment_field_faithful

instance metacicNormalizationAuditNontrivial :
    BEDC.Meta.TasteGate.Nontrivial MetacicNormalizationAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetacicNormalizationAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetacicNormalizationAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def metacicNormalizationAuditTasteGate :
    ChapterTasteGate MetacicNormalizationAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metacicNormalizationAuditChapterTasteGate

theorem MetacicNormalizationAuditTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate MetacicNormalizationAuditUp) ∧
      Nonempty (FieldFaithful MetacicNormalizationAuditUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial MetacicNormalizationAuditUp) ∧
          (∀ h : BHist,
            metacicNormalizationAuditDecodeBHist (metacicNormalizationAuditEncodeBHist h) = h) ∧
            metacicNormalizationAuditEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨metacicNormalizationAuditChapterTasteGate⟩
  · constructor
    · exact ⟨metacicNormalizationAuditFieldFaithful⟩
    · constructor
      · exact ⟨metacicNormalizationAuditNontrivial⟩
      · constructor
        · exact MetacicNormalizationAuditTasteGate_single_carrier_alignment_decode_encode
        · rfl

end BEDC.Derived.MetacicNormalizationAuditUp
