import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GaloisExtUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GaloisExtUp : Type where
  | mk :
      (fieldExt separable normality separability automorphism classifier provenance
        endpoint : BHist) ->
        GaloisExtUp
  deriving DecidableEq

def galoisExtEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: galoisExtEncodeBHist h
  | BHist.e1 h => BMark.b1 :: galoisExtEncodeBHist h

def galoisExtDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (galoisExtDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (galoisExtDecodeBHist tail)

theorem GaloisExtTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, galoisExtDecodeBHist (galoisExtEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def galoisExtFields : GaloisExtUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GaloisExtUp.mk fieldExt separable normality separability automorphism classifier
      provenance endpoint =>
      [fieldExt, separable, normality, separability, automorphism, classifier, provenance,
        endpoint]

def galoisExtToEventFlow : GaloisExtUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (galoisExtFields x).map galoisExtEncodeBHist

def galoisExtFromEventFlow : EventFlow -> Option GaloisExtUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | fieldExt :: rest0 =>
      match rest0 with
      | [] => none
      | separable :: rest1 =>
          match rest1 with
          | [] => none
          | normality :: rest2 =>
              match rest2 with
              | [] => none
              | separability :: rest3 =>
                  match rest3 with
                  | [] => none
                  | automorphism :: rest4 =>
                      match rest4 with
                      | [] => none
                      | classifier :: rest5 =>
                          match rest5 with
                          | [] => none
                          | provenance :: rest6 =>
                              match rest6 with
                              | [] => none
                              | endpoint :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some
                                        (GaloisExtUp.mk
                                          (galoisExtDecodeBHist fieldExt)
                                          (galoisExtDecodeBHist separable)
                                          (galoisExtDecodeBHist normality)
                                          (galoisExtDecodeBHist separability)
                                          (galoisExtDecodeBHist automorphism)
                                          (galoisExtDecodeBHist classifier)
                                          (galoisExtDecodeBHist provenance)
                                          (galoisExtDecodeBHist endpoint))
                                  | _ :: _ => none

theorem GaloisExtTasteGate_single_carrier_alignment_round_trip :
    forall x : GaloisExtUp, galoisExtFromEventFlow (galoisExtToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk fieldExt separable normality separability automorphism classifier provenance endpoint =>
      change
        some
          (GaloisExtUp.mk
            (galoisExtDecodeBHist (galoisExtEncodeBHist fieldExt))
            (galoisExtDecodeBHist (galoisExtEncodeBHist separable))
            (galoisExtDecodeBHist (galoisExtEncodeBHist normality))
            (galoisExtDecodeBHist (galoisExtEncodeBHist separability))
            (galoisExtDecodeBHist (galoisExtEncodeBHist automorphism))
            (galoisExtDecodeBHist (galoisExtEncodeBHist classifier))
            (galoisExtDecodeBHist (galoisExtEncodeBHist provenance))
            (galoisExtDecodeBHist (galoisExtEncodeBHist endpoint))) =
          some
            (GaloisExtUp.mk fieldExt separable normality separability automorphism classifier
              provenance endpoint)
      rw [GaloisExtTasteGate_single_carrier_alignment_decode_encode fieldExt,
        GaloisExtTasteGate_single_carrier_alignment_decode_encode separable,
        GaloisExtTasteGate_single_carrier_alignment_decode_encode normality,
        GaloisExtTasteGate_single_carrier_alignment_decode_encode separability,
        GaloisExtTasteGate_single_carrier_alignment_decode_encode automorphism,
        GaloisExtTasteGate_single_carrier_alignment_decode_encode classifier,
        GaloisExtTasteGate_single_carrier_alignment_decode_encode provenance,
        GaloisExtTasteGate_single_carrier_alignment_decode_encode endpoint]

theorem GaloisExtTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : GaloisExtUp} :
    galoisExtToEventFlow x = galoisExtToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      galoisExtFromEventFlow (galoisExtToEventFlow x) =
        galoisExtFromEventFlow (galoisExtToEventFlow y) :=
    congrArg galoisExtFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (GaloisExtTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (GaloisExtTasteGate_single_carrier_alignment_round_trip y)))

theorem GaloisExtTasteGate_single_carrier_alignment_field_faithful :
    forall x y : GaloisExtUp, galoisExtFields x = galoisExtFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk fieldExt₁ separable₁ normality₁ separability₁ automorphism₁ classifier₁ provenance₁
      endpoint₁ =>
      cases y with
      | mk fieldExt₂ separable₂ normality₂ separability₂ automorphism₂ classifier₂ provenance₂
          endpoint₂ =>
          cases hfields
          rfl

instance galoisExtBHistCarrier : BHistCarrier GaloisExtUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := galoisExtToEventFlow
  fromEventFlow := galoisExtFromEventFlow

instance galoisExtChapterTasteGate : ChapterTasteGate GaloisExtUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x =>
    id (GaloisExtTasteGate_single_carrier_alignment_round_trip x)
  layer_separation := by
    intro x y hxy heq
    exact hxy (GaloisExtTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance galoisExtFieldFaithful : FieldFaithful GaloisExtUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := galoisExtFields
  field_faithful := GaloisExtTasteGate_single_carrier_alignment_field_faithful

instance galoisExtNontrivial : Nontrivial GaloisExtUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨GaloisExtUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      GaloisExtUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate GaloisExtUp :=
  -- BEDC touchpoint anchor: BHist BMark
  galoisExtChapterTasteGate

theorem GaloisExtTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate GaloisExtUp) ∧
      Nonempty (FieldFaithful GaloisExtUp) ∧
        Nonempty (Nontrivial GaloisExtUp) ∧
          (∀ h : BHist, galoisExtDecodeBHist (galoisExtEncodeBHist h) = h) ∧
            (∀ x : GaloisExtUp, galoisExtFromEventFlow (galoisExtToEventFlow x) = some x) ∧
              (∀ x y : GaloisExtUp,
                galoisExtToEventFlow x = galoisExtToEventFlow y -> x = y) ∧
                galoisExtEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨galoisExtChapterTasteGate⟩
  · constructor
    · exact ⟨galoisExtFieldFaithful⟩
    · constructor
      · exact ⟨galoisExtNontrivial⟩
      · constructor
        · exact GaloisExtTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact GaloisExtTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact GaloisExtTasteGate_single_carrier_alignment_toEventFlow_injective heq
            · rfl

end BEDC.Derived.GaloisExtUp.TasteGate
