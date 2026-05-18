import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RecursorBranchCompletenessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RecursorBranchCompletenessUp : Type where
  | mk :
      (signature recursor motive branches completeness transport replay provenance nameCert :
        BHist) →
      RecursorBranchCompletenessUp
  deriving DecidableEq

def recursorBranchCompletenessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: recursorBranchCompletenessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: recursorBranchCompletenessEncodeBHist h

def recursorBranchCompletenessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (recursorBranchCompletenessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (recursorBranchCompletenessDecodeBHist tail)

private theorem recursorBranchCompleteness_decode_encode_bhist :
    ∀ h : BHist,
      recursorBranchCompletenessDecodeBHist
        (recursorBranchCompletenessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def recursorBranchCompletenessToEventFlow : RecursorBranchCompletenessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RecursorBranchCompletenessUp.mk signature recursor motive branches completeness transport
      replay provenance nameCert =>
      [[BMark.b0],
        recursorBranchCompletenessEncodeBHist signature,
        [BMark.b1, BMark.b0],
        recursorBranchCompletenessEncodeBHist recursor,
        [BMark.b1, BMark.b1, BMark.b0],
        recursorBranchCompletenessEncodeBHist motive,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        recursorBranchCompletenessEncodeBHist branches,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        recursorBranchCompletenessEncodeBHist completeness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        recursorBranchCompletenessEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        recursorBranchCompletenessEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        recursorBranchCompletenessEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        recursorBranchCompletenessEncodeBHist nameCert]

def recursorBranchCompletenessFromEventFlow :
    EventFlow → Option RecursorBranchCompletenessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | signature :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | recursor :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | motive :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | branches :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | completeness :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | replay :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance ::
                                                                  rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 ::
                                                                      rest16 =>
                                                                      match
                                                                        rest16
                                                                      with
                                                                      | [] =>
                                                                          none
                                                                      | nameCert ::
                                                                          rest17 =>
                                                                          match
                                                                            rest17
                                                                          with
                                                                          | [] =>
                                                                              some
                                                                                (RecursorBranchCompletenessUp.mk
                                                                                  (recursorBranchCompletenessDecodeBHist
                                                                                    signature)
                                                                                  (recursorBranchCompletenessDecodeBHist
                                                                                    recursor)
                                                                                  (recursorBranchCompletenessDecodeBHist
                                                                                    motive)
                                                                                  (recursorBranchCompletenessDecodeBHist
                                                                                    branches)
                                                                                  (recursorBranchCompletenessDecodeBHist
                                                                                    completeness)
                                                                                  (recursorBranchCompletenessDecodeBHist
                                                                                    transport)
                                                                                  (recursorBranchCompletenessDecodeBHist
                                                                                    replay)
                                                                                  (recursorBranchCompletenessDecodeBHist
                                                                                    provenance)
                                                                                  (recursorBranchCompletenessDecodeBHist
                                                                                    nameCert))
                                                                          | _ :: _ =>
                                                                              none

private theorem recursorBranchCompleteness_round_trip :
    ∀ x : RecursorBranchCompletenessUp,
      recursorBranchCompletenessFromEventFlow
        (recursorBranchCompletenessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk signature recursor motive branches completeness transport replay provenance nameCert =>
      change
        some
          (RecursorBranchCompletenessUp.mk
            (recursorBranchCompletenessDecodeBHist
              (recursorBranchCompletenessEncodeBHist signature))
            (recursorBranchCompletenessDecodeBHist
              (recursorBranchCompletenessEncodeBHist recursor))
            (recursorBranchCompletenessDecodeBHist
              (recursorBranchCompletenessEncodeBHist motive))
            (recursorBranchCompletenessDecodeBHist
              (recursorBranchCompletenessEncodeBHist branches))
            (recursorBranchCompletenessDecodeBHist
              (recursorBranchCompletenessEncodeBHist completeness))
            (recursorBranchCompletenessDecodeBHist
              (recursorBranchCompletenessEncodeBHist transport))
            (recursorBranchCompletenessDecodeBHist
              (recursorBranchCompletenessEncodeBHist replay))
            (recursorBranchCompletenessDecodeBHist
              (recursorBranchCompletenessEncodeBHist provenance))
            (recursorBranchCompletenessDecodeBHist
              (recursorBranchCompletenessEncodeBHist nameCert))) =
          some
            (RecursorBranchCompletenessUp.mk signature recursor motive branches completeness
              transport replay provenance nameCert)
      rw [recursorBranchCompleteness_decode_encode_bhist signature,
        recursorBranchCompleteness_decode_encode_bhist recursor,
        recursorBranchCompleteness_decode_encode_bhist motive,
        recursorBranchCompleteness_decode_encode_bhist branches,
        recursorBranchCompleteness_decode_encode_bhist completeness,
        recursorBranchCompleteness_decode_encode_bhist transport,
        recursorBranchCompleteness_decode_encode_bhist replay,
        recursorBranchCompleteness_decode_encode_bhist provenance,
        recursorBranchCompleteness_decode_encode_bhist nameCert]

private theorem recursorBranchCompletenessToEventFlow_injective
    {x y : RecursorBranchCompletenessUp} :
    recursorBranchCompletenessToEventFlow x =
      recursorBranchCompletenessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      recursorBranchCompletenessFromEventFlow (recursorBranchCompletenessToEventFlow x) =
        recursorBranchCompletenessFromEventFlow (recursorBranchCompletenessToEventFlow y) :=
    congrArg recursorBranchCompletenessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (recursorBranchCompleteness_round_trip x).symm
      (Eq.trans hread (recursorBranchCompleteness_round_trip y)))

def recursorBranchCompletenessFields : RecursorBranchCompletenessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RecursorBranchCompletenessUp.mk signature recursor motive branches completeness transport
      replay provenance nameCert =>
      [signature, recursor, motive, branches, completeness, transport, replay, provenance,
        nameCert]

private theorem recursorBranchCompleteness_field_faithful :
    ∀ x y : RecursorBranchCompletenessUp,
      recursorBranchCompletenessFields x = recursorBranchCompletenessFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk signature recursor motive branches completeness transport replay provenance nameCert =>
      cases y with
      | mk signature' recursor' motive' branches' completeness' transport' replay'
          provenance' nameCert' =>
          cases hfields
          rfl

instance recursorBranchCompletenessBHistCarrier :
    BHistCarrier RecursorBranchCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := recursorBranchCompletenessToEventFlow
  fromEventFlow := recursorBranchCompletenessFromEventFlow

instance recursorBranchCompletenessChapterTasteGate :
    ChapterTasteGate RecursorBranchCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      recursorBranchCompletenessFromEventFlow
        (recursorBranchCompletenessToEventFlow x) = some x
    exact recursorBranchCompleteness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (recursorBranchCompletenessToEventFlow_injective heq)

instance recursorBranchCompletenessFieldFaithful :
    FieldFaithful RecursorBranchCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := recursorBranchCompletenessFields
  field_faithful := recursorBranchCompleteness_field_faithful

instance recursorBranchCompletenessNontrivial : Nontrivial RecursorBranchCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RecursorBranchCompletenessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RecursorBranchCompletenessUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RecursorBranchCompletenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  recursorBranchCompletenessChapterTasteGate

def taste_gate_witness : FieldFaithful RecursorBranchCompletenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  recursorBranchCompletenessFieldFaithful

theorem RecursorBranchCompletenessTasteGate_single_carrier_alignment :
    (∀ h : BHist, recursorBranchCompletenessDecodeBHist
      (recursorBranchCompletenessEncodeBHist h) = h) ∧
      (∀ x : RecursorBranchCompletenessUp,
        recursorBranchCompletenessFromEventFlow
          (recursorBranchCompletenessToEventFlow x) = some x) ∧
        (∀ x y : RecursorBranchCompletenessUp,
          recursorBranchCompletenessToEventFlow x =
            recursorBranchCompletenessToEventFlow y → x = y) ∧
          recursorBranchCompletenessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact recursorBranchCompleteness_decode_encode_bhist
  · constructor
    · exact recursorBranchCompleteness_round_trip
    · constructor
      · intro x y heq
        exact recursorBranchCompletenessToEventFlow_injective heq
      · rfl

namespace TasteGate

theorem RecursorBranchCompletenessTasteGate_single_carrier_alignment :
    (∀ h : BHist, recursorBranchCompletenessDecodeBHist
      (recursorBranchCompletenessEncodeBHist h) = h) ∧
      (∀ x : RecursorBranchCompletenessUp,
        recursorBranchCompletenessFromEventFlow
          (recursorBranchCompletenessToEventFlow x) = some x) ∧
        Nonempty (ChapterTasteGate RecursorBranchCompletenessUp) ∧
          recursorBranchCompletenessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨recursorBranchCompleteness_decode_encode_bhist,
      recursorBranchCompleteness_round_trip,
      ⟨recursorBranchCompletenessChapterTasteGate⟩,
      rfl⟩

end TasteGate

end BEDC.Derived.RecursorBranchCompletenessUp
