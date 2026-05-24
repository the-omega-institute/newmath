import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AbGroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AbGroupUp : Type where
  | mk :
      (carrier operation identity inverse commutativity classifier provenance endpoint :
        BHist) ->
        AbGroupUp
  deriving DecidableEq

def abGroupEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: abGroupEncodeBHist h
  | BHist.e1 h => BMark.b1 :: abGroupEncodeBHist h

def abGroupDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (abGroupDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (abGroupDecodeBHist tail)

theorem AbGroupTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, abGroupDecodeBHist (abGroupEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def abGroupFields : AbGroupUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AbGroupUp.mk carrier operation identity inverse commutativity classifier provenance endpoint =>
      [carrier, operation, identity, inverse, commutativity, classifier, provenance, endpoint]

def abGroupToEventFlow : AbGroupUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (abGroupFields x).map abGroupEncodeBHist

def abGroupFromEventFlow : EventFlow -> Option AbGroupUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | carrier :: rest0 =>
      match rest0 with
      | [] => none
      | operation :: rest1 =>
          match rest1 with
          | [] => none
          | identity :: rest2 =>
              match rest2 with
              | [] => none
              | inverse :: rest3 =>
                  match rest3 with
                  | [] => none
                  | commutativity :: rest4 =>
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
                                        (AbGroupUp.mk
                                          (abGroupDecodeBHist carrier)
                                          (abGroupDecodeBHist operation)
                                          (abGroupDecodeBHist identity)
                                          (abGroupDecodeBHist inverse)
                                          (abGroupDecodeBHist commutativity)
                                          (abGroupDecodeBHist classifier)
                                          (abGroupDecodeBHist provenance)
                                          (abGroupDecodeBHist endpoint))
                                  | _ :: _ => none

theorem AbGroupTasteGate_single_carrier_alignment_round_trip :
    forall x : AbGroupUp, abGroupFromEventFlow (abGroupToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk carrier operation identity inverse commutativity classifier provenance endpoint =>
      change
        some
          (AbGroupUp.mk
            (abGroupDecodeBHist (abGroupEncodeBHist carrier))
            (abGroupDecodeBHist (abGroupEncodeBHist operation))
            (abGroupDecodeBHist (abGroupEncodeBHist identity))
            (abGroupDecodeBHist (abGroupEncodeBHist inverse))
            (abGroupDecodeBHist (abGroupEncodeBHist commutativity))
            (abGroupDecodeBHist (abGroupEncodeBHist classifier))
            (abGroupDecodeBHist (abGroupEncodeBHist provenance))
            (abGroupDecodeBHist (abGroupEncodeBHist endpoint))) =
          some
            (AbGroupUp.mk carrier operation identity inverse commutativity classifier provenance
              endpoint)
      rw [AbGroupTasteGate_single_carrier_alignment_decode_encode carrier,
        AbGroupTasteGate_single_carrier_alignment_decode_encode operation,
        AbGroupTasteGate_single_carrier_alignment_decode_encode identity,
        AbGroupTasteGate_single_carrier_alignment_decode_encode inverse,
        AbGroupTasteGate_single_carrier_alignment_decode_encode commutativity,
        AbGroupTasteGate_single_carrier_alignment_decode_encode classifier,
        AbGroupTasteGate_single_carrier_alignment_decode_encode provenance,
        AbGroupTasteGate_single_carrier_alignment_decode_encode endpoint]

theorem AbGroupTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AbGroupUp} :
    abGroupToEventFlow x = abGroupToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      abGroupFromEventFlow (abGroupToEventFlow x) =
        abGroupFromEventFlow (abGroupToEventFlow y) :=
    congrArg abGroupFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (AbGroupTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (AbGroupTasteGate_single_carrier_alignment_round_trip y)))

theorem AbGroupTasteGate_single_carrier_alignment_field_faithful :
    forall x y : AbGroupUp, abGroupFields x = abGroupFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk carrier₁ operation₁ identity₁ inverse₁ commutativity₁ classifier₁ provenance₁ endpoint₁ =>
      cases y with
      | mk carrier₂ operation₂ identity₂ inverse₂ commutativity₂ classifier₂ provenance₂
          endpoint₂ =>
          cases hfields
          rfl

instance abGroupBHistCarrier : BHistCarrier AbGroupUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := abGroupToEventFlow
  fromEventFlow := abGroupFromEventFlow

instance abGroupChapterTasteGate : ChapterTasteGate AbGroupUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x =>
    id (AbGroupTasteGate_single_carrier_alignment_round_trip x)
  layer_separation := by
    intro x y hxy heq
    exact hxy (AbGroupTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance abGroupFieldFaithful : FieldFaithful AbGroupUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := abGroupFields
  field_faithful := AbGroupTasteGate_single_carrier_alignment_field_faithful

instance abGroupNontrivial : BEDC.Meta.TasteGate.Nontrivial AbGroupUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AbGroupUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      AbGroupUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def abGroupTasteGate : ChapterTasteGate AbGroupUp :=
  -- BEDC touchpoint anchor: BHist BMark
  abGroupChapterTasteGate

theorem AbGroupTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate AbGroupUp) ∧
      Nonempty (FieldFaithful AbGroupUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial AbGroupUp) ∧
          (∀ h : BHist, abGroupDecodeBHist (abGroupEncodeBHist h) = h) ∧
            (∀ x : AbGroupUp, abGroupFromEventFlow (abGroupToEventFlow x) = some x) ∧
              (∀ x y : AbGroupUp,
                abGroupToEventFlow x = abGroupToEventFlow y -> x = y) ∧
                abGroupEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨abGroupChapterTasteGate⟩
  · constructor
    · exact ⟨abGroupFieldFaithful⟩
    · constructor
      · exact ⟨abGroupNontrivial⟩
      · constructor
        · exact AbGroupTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact AbGroupTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact AbGroupTasteGate_single_carrier_alignment_toEventFlow_injective heq
            · rfl

end BEDC.Derived.AbGroupUp
