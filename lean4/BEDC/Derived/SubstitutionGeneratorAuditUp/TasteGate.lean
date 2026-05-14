import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SubstitutionGeneratorAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SubstitutionGeneratorAuditUp : Type where
  | mk (term closedBoundary closedShift closedSubstitution closedComposition replay
      transport continuation provenance name : BHist) :
      SubstitutionGeneratorAuditUp
  deriving DecidableEq

def substitutionGeneratorAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: substitutionGeneratorAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: substitutionGeneratorAuditEncodeBHist h

def substitutionGeneratorAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (substitutionGeneratorAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (substitutionGeneratorAuditDecodeBHist tail)

private theorem substitutionGeneratorAuditDecode_encode_bhist :
    ∀ h : BHist,
      substitutionGeneratorAuditDecodeBHist (substitutionGeneratorAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def substitutionGeneratorAuditToEventFlow : SubstitutionGeneratorAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SubstitutionGeneratorAuditUp.mk term closedBoundary closedShift closedSubstitution
      closedComposition replay transport continuation provenance name =>
      [[BMark.b0],
        substitutionGeneratorAuditEncodeBHist term,
        [BMark.b1, BMark.b0],
        substitutionGeneratorAuditEncodeBHist closedBoundary,
        [BMark.b1, BMark.b1, BMark.b0],
        substitutionGeneratorAuditEncodeBHist closedShift,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        substitutionGeneratorAuditEncodeBHist closedSubstitution,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        substitutionGeneratorAuditEncodeBHist closedComposition,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        substitutionGeneratorAuditEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        substitutionGeneratorAuditEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        substitutionGeneratorAuditEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        substitutionGeneratorAuditEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        substitutionGeneratorAuditEncodeBHist name]

def substitutionGeneratorAuditFromEventFlow :
    EventFlow → Option SubstitutionGeneratorAuditUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | term :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | closedBoundary :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | closedShift :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | closedSubstitution :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | closedComposition :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | replay :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | continuation :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | name :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (SubstitutionGeneratorAuditUp.mk
                                                                                          (substitutionGeneratorAuditDecodeBHist
                                                                                            term)
                                                                                          (substitutionGeneratorAuditDecodeBHist
                                                                                            closedBoundary)
                                                                                          (substitutionGeneratorAuditDecodeBHist
                                                                                            closedShift)
                                                                                          (substitutionGeneratorAuditDecodeBHist
                                                                                            closedSubstitution)
                                                                                          (substitutionGeneratorAuditDecodeBHist
                                                                                            closedComposition)
                                                                                          (substitutionGeneratorAuditDecodeBHist
                                                                                            replay)
                                                                                          (substitutionGeneratorAuditDecodeBHist
                                                                                            transport)
                                                                                          (substitutionGeneratorAuditDecodeBHist
                                                                                            continuation)
                                                                                          (substitutionGeneratorAuditDecodeBHist
                                                                                            provenance)
                                                                                          (substitutionGeneratorAuditDecodeBHist
                                                                                            name))
                                                                                  | _ :: _ => none

private theorem substitutionGeneratorAudit_round_trip :
    ∀ x : SubstitutionGeneratorAuditUp,
      substitutionGeneratorAuditFromEventFlow
        (substitutionGeneratorAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk term closedBoundary closedShift closedSubstitution closedComposition replay transport
      continuation provenance name =>
      change
        some
          (SubstitutionGeneratorAuditUp.mk
            (substitutionGeneratorAuditDecodeBHist
              (substitutionGeneratorAuditEncodeBHist term))
            (substitutionGeneratorAuditDecodeBHist
              (substitutionGeneratorAuditEncodeBHist closedBoundary))
            (substitutionGeneratorAuditDecodeBHist
              (substitutionGeneratorAuditEncodeBHist closedShift))
            (substitutionGeneratorAuditDecodeBHist
              (substitutionGeneratorAuditEncodeBHist closedSubstitution))
            (substitutionGeneratorAuditDecodeBHist
              (substitutionGeneratorAuditEncodeBHist closedComposition))
            (substitutionGeneratorAuditDecodeBHist
              (substitutionGeneratorAuditEncodeBHist replay))
            (substitutionGeneratorAuditDecodeBHist
              (substitutionGeneratorAuditEncodeBHist transport))
            (substitutionGeneratorAuditDecodeBHist
              (substitutionGeneratorAuditEncodeBHist continuation))
            (substitutionGeneratorAuditDecodeBHist
              (substitutionGeneratorAuditEncodeBHist provenance))
            (substitutionGeneratorAuditDecodeBHist
              (substitutionGeneratorAuditEncodeBHist name))) =
          some
            (SubstitutionGeneratorAuditUp.mk term closedBoundary closedShift
              closedSubstitution closedComposition replay transport continuation provenance name)
      rw [substitutionGeneratorAuditDecode_encode_bhist term,
        substitutionGeneratorAuditDecode_encode_bhist closedBoundary,
        substitutionGeneratorAuditDecode_encode_bhist closedShift,
        substitutionGeneratorAuditDecode_encode_bhist closedSubstitution,
        substitutionGeneratorAuditDecode_encode_bhist closedComposition,
        substitutionGeneratorAuditDecode_encode_bhist replay,
        substitutionGeneratorAuditDecode_encode_bhist transport,
        substitutionGeneratorAuditDecode_encode_bhist continuation,
        substitutionGeneratorAuditDecode_encode_bhist provenance,
        substitutionGeneratorAuditDecode_encode_bhist name]

theorem substitutionGeneratorAuditToEventFlow_injective
    {x y : SubstitutionGeneratorAuditUp} :
    substitutionGeneratorAuditToEventFlow x = substitutionGeneratorAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      substitutionGeneratorAuditFromEventFlow (substitutionGeneratorAuditToEventFlow x) =
        substitutionGeneratorAuditFromEventFlow (substitutionGeneratorAuditToEventFlow y) :=
    congrArg substitutionGeneratorAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (substitutionGeneratorAudit_round_trip x).symm
      (Eq.trans hread (substitutionGeneratorAudit_round_trip y)))

instance substitutionGeneratorAuditBHistCarrier :
    BHistCarrier SubstitutionGeneratorAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := substitutionGeneratorAuditToEventFlow
  fromEventFlow := substitutionGeneratorAuditFromEventFlow

instance substitutionGeneratorAuditChapterTasteGate :
    ChapterTasteGate SubstitutionGeneratorAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change substitutionGeneratorAuditFromEventFlow (substitutionGeneratorAuditToEventFlow x) =
      some x
    exact substitutionGeneratorAudit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (substitutionGeneratorAuditToEventFlow_injective heq)

instance substitutionGeneratorAuditFieldFaithful :
    FieldFaithful SubstitutionGeneratorAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | SubstitutionGeneratorAuditUp.mk term closedBoundary closedShift closedSubstitution
        closedComposition replay transport continuation provenance name =>
        [term, closedBoundary, closedShift, closedSubstitution, closedComposition, replay,
          transport, continuation, provenance, name]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk term₁ closedBoundary₁ closedShift₁ closedSubstitution₁ closedComposition₁ replay₁
        transport₁ continuation₁ provenance₁ name₁ =>
        cases y with
        | mk term₂ closedBoundary₂ closedShift₂ closedSubstitution₂ closedComposition₂ replay₂
            transport₂ continuation₂ provenance₂ name₂ =>
            cases h
            rfl

instance substitutionGeneratorAuditNontrivial : Nontrivial SubstitutionGeneratorAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SubstitutionGeneratorAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SubstitutionGeneratorAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem SubstitutionGeneratorAuditTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate SubstitutionGeneratorAuditUp) ∧
      Nonempty (FieldFaithful SubstitutionGeneratorAuditUp) ∧
        Nonempty (Nontrivial SubstitutionGeneratorAuditUp) ∧
          (∀ x : SubstitutionGeneratorAuditUp,
            substitutionGeneratorAuditFromEventFlow (substitutionGeneratorAuditToEventFlow x) =
              some x) ∧
            (∀ x y : SubstitutionGeneratorAuditUp,
              substitutionGeneratorAuditToEventFlow x =
                substitutionGeneratorAuditToEventFlow y → x = y) ∧
              substitutionGeneratorAuditEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨substitutionGeneratorAuditChapterTasteGate⟩
  · constructor
    · exact ⟨substitutionGeneratorAuditFieldFaithful⟩
    · constructor
      · exact ⟨substitutionGeneratorAuditNontrivial⟩
      · constructor
        · exact substitutionGeneratorAudit_round_trip
        · constructor
          · intro x y heq
            exact substitutionGeneratorAuditToEventFlow_injective heq
          · rfl

end BEDC.Derived.SubstitutionGeneratorAuditUp
