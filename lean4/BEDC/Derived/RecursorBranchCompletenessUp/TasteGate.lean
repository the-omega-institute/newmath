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
      (signature recursor motive branches completeness transport continuation provenance
        nameCert : BHist) ->
      RecursorBranchCompletenessUp
  deriving DecidableEq

def recursorBranchCompletenessEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: recursorBranchCompletenessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: recursorBranchCompletenessEncodeBHist h

def recursorBranchCompletenessDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (recursorBranchCompletenessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (recursorBranchCompletenessDecodeBHist tail)

private theorem recursorBranchCompletenessDecodeEncodeBHist :
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

def recursorBranchCompletenessFields :
    RecursorBranchCompletenessUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RecursorBranchCompletenessUp.mk signature recursor motive branches completeness transport
      continuation provenance nameCert =>
      [signature, recursor, motive, branches, completeness, transport, continuation,
        provenance, nameCert]

def recursorBranchCompletenessToEventFlow :
    RecursorBranchCompletenessUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RecursorBranchCompletenessUp.mk signature recursor motive branches completeness transport
      continuation provenance nameCert =>
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
        recursorBranchCompletenessEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        recursorBranchCompletenessEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        recursorBranchCompletenessEncodeBHist nameCert]

def recursorBranchCompletenessFromEventFlow :
    EventFlow -> Option RecursorBranchCompletenessUp
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
                                                      | continuation :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | nameCert ::
                                                                          rest17 =>
                                                                          match rest17
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
                                                                                    continuation)
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
  | mk signature recursor motive branches completeness transport continuation provenance
      nameCert =>
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
              (recursorBranchCompletenessEncodeBHist continuation))
            (recursorBranchCompletenessDecodeBHist
              (recursorBranchCompletenessEncodeBHist provenance))
            (recursorBranchCompletenessDecodeBHist
              (recursorBranchCompletenessEncodeBHist nameCert))) =
          some
            (RecursorBranchCompletenessUp.mk signature recursor motive branches completeness
              transport continuation provenance nameCert)
      rw [recursorBranchCompletenessDecodeEncodeBHist signature,
        recursorBranchCompletenessDecodeEncodeBHist recursor,
        recursorBranchCompletenessDecodeEncodeBHist motive,
        recursorBranchCompletenessDecodeEncodeBHist branches,
        recursorBranchCompletenessDecodeEncodeBHist completeness,
        recursorBranchCompletenessDecodeEncodeBHist transport,
        recursorBranchCompletenessDecodeEncodeBHist continuation,
        recursorBranchCompletenessDecodeEncodeBHist provenance,
        recursorBranchCompletenessDecodeEncodeBHist nameCert]

private theorem recursorBranchCompletenessToEventFlow_injective
    {x y : RecursorBranchCompletenessUp} :
    recursorBranchCompletenessToEventFlow x =
        recursorBranchCompletenessToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      recursorBranchCompletenessFromEventFlow
          (recursorBranchCompletenessToEventFlow x) =
        recursorBranchCompletenessFromEventFlow
          (recursorBranchCompletenessToEventFlow y) :=
    congrArg recursorBranchCompletenessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (recursorBranchCompleteness_round_trip x).symm
      (Eq.trans hread (recursorBranchCompleteness_round_trip y)))

private theorem recursorBranchCompleteness_fields_faithful :
    ∀ x y : RecursorBranchCompletenessUp,
      recursorBranchCompletenessFields x =
        recursorBranchCompletenessFields y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk signature recursor motive branches completeness transport continuation provenance
      nameCert =>
      cases y with
      | mk signature' recursor' motive' branches' completeness' transport' continuation'
          provenance' nameCert' =>
          injection hfields with hSignature hTail0
          injection hTail0 with hRecursor hTail1
          injection hTail1 with hMotive hTail2
          injection hTail2 with hBranches hTail3
          injection hTail3 with hCompleteness hTail4
          injection hTail4 with hTransport hTail5
          injection hTail5 with hContinuation hTail6
          injection hTail6 with hProvenance hTail7
          injection hTail7 with hNameCert _hNil
          cases hSignature
          cases hRecursor
          cases hMotive
          cases hBranches
          cases hCompleteness
          cases hTransport
          cases hContinuation
          cases hProvenance
          cases hNameCert
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
  field_faithful := recursorBranchCompleteness_fields_faithful

instance recursorBranchCompletenessNontrivial :
    Nontrivial RecursorBranchCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RecursorBranchCompletenessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RecursorBranchCompletenessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RecursorBranchCompletenessNameCertObligations :
    Nonempty (ChapterTasteGate RecursorBranchCompletenessUp) ∧
      Nonempty (FieldFaithful RecursorBranchCompletenessUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RecursorBranchCompletenessUp) ∧
          (∀ h : BHist,
            recursorBranchCompletenessDecodeBHist
              (recursorBranchCompletenessEncodeBHist h) = h) ∧
            recursorBranchCompletenessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨recursorBranchCompletenessChapterTasteGate⟩,
      ⟨⟨recursorBranchCompletenessFieldFaithful⟩,
        ⟨⟨recursorBranchCompletenessNontrivial⟩,
          ⟨recursorBranchCompletenessDecodeEncodeBHist, rfl⟩⟩⟩⟩

end BEDC.Derived.RecursorBranchCompletenessUp
