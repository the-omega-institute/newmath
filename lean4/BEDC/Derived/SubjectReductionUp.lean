import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SubjectReductionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SubjectReductionUp : Type where
  | mk :
      (source target sourceExt reduction targetExt ledger sameTransport routes provenance
        localName : BHist) →
        SubjectReductionUp
  deriving DecidableEq

def subjectReductionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: subjectReductionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: subjectReductionEncodeBHist h

def subjectReductionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (subjectReductionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (subjectReductionDecodeBHist tail)

private theorem subjectReductionDecode_encode_bhist :
    ∀ h : BHist, subjectReductionDecodeBHist (subjectReductionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def subjectReductionToEventFlow : SubjectReductionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SubjectReductionUp.mk source target sourceExt reduction targetExt ledger sameTransport
      routes provenance localName =>
      [[BMark.b0],
        subjectReductionEncodeBHist source,
        [BMark.b1, BMark.b0],
        subjectReductionEncodeBHist target,
        [BMark.b1, BMark.b1, BMark.b0],
        subjectReductionEncodeBHist sourceExt,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subjectReductionEncodeBHist reduction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subjectReductionEncodeBHist targetExt,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subjectReductionEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subjectReductionEncodeBHist sameTransport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        subjectReductionEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        subjectReductionEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        subjectReductionEncodeBHist localName]

def subjectReductionFromEventFlow : EventFlow → Option SubjectReductionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | source :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | target :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | sourceExt :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | reduction :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | targetExt :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | ledger :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | sameTransport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | routes :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance ::
                                                                          rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match rest18 with
                                                                              | [] =>
                                                                                  none
                                                                              | localName ::
                                                                                  rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (SubjectReductionUp.mk
                                                                                          (subjectReductionDecodeBHist
                                                                                            source)
                                                                                          (subjectReductionDecodeBHist
                                                                                            target)
                                                                                          (subjectReductionDecodeBHist
                                                                                            sourceExt)
                                                                                          (subjectReductionDecodeBHist
                                                                                            reduction)
                                                                                          (subjectReductionDecodeBHist
                                                                                            targetExt)
                                                                                          (subjectReductionDecodeBHist
                                                                                            ledger)
                                                                                          (subjectReductionDecodeBHist
                                                                                            sameTransport)
                                                                                          (subjectReductionDecodeBHist
                                                                                            routes)
                                                                                          (subjectReductionDecodeBHist
                                                                                            provenance)
                                                                                          (subjectReductionDecodeBHist
                                                                                            localName))
                                                                                  | _ :: _ =>
                                                                                      none

private theorem subjectReduction_round_trip :
    ∀ x : SubjectReductionUp,
      subjectReductionFromEventFlow (subjectReductionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target sourceExt reduction targetExt ledger sameTransport routes provenance
      localName =>
      change
        some
          (SubjectReductionUp.mk
            (subjectReductionDecodeBHist (subjectReductionEncodeBHist source))
            (subjectReductionDecodeBHist (subjectReductionEncodeBHist target))
            (subjectReductionDecodeBHist (subjectReductionEncodeBHist sourceExt))
            (subjectReductionDecodeBHist (subjectReductionEncodeBHist reduction))
            (subjectReductionDecodeBHist (subjectReductionEncodeBHist targetExt))
            (subjectReductionDecodeBHist (subjectReductionEncodeBHist ledger))
            (subjectReductionDecodeBHist (subjectReductionEncodeBHist sameTransport))
            (subjectReductionDecodeBHist (subjectReductionEncodeBHist routes))
            (subjectReductionDecodeBHist (subjectReductionEncodeBHist provenance))
            (subjectReductionDecodeBHist (subjectReductionEncodeBHist localName))) =
          some
            (SubjectReductionUp.mk source target sourceExt reduction targetExt ledger
              sameTransport routes provenance localName)
      rw [subjectReductionDecode_encode_bhist source,
        subjectReductionDecode_encode_bhist target,
        subjectReductionDecode_encode_bhist sourceExt,
        subjectReductionDecode_encode_bhist reduction,
        subjectReductionDecode_encode_bhist targetExt,
        subjectReductionDecode_encode_bhist ledger,
        subjectReductionDecode_encode_bhist sameTransport,
        subjectReductionDecode_encode_bhist routes,
        subjectReductionDecode_encode_bhist provenance,
        subjectReductionDecode_encode_bhist localName]

private theorem subjectReductionToEventFlow_injective {x y : SubjectReductionUp} :
    subjectReductionToEventFlow x = subjectReductionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      subjectReductionFromEventFlow (subjectReductionToEventFlow x) =
        subjectReductionFromEventFlow (subjectReductionToEventFlow y) :=
    congrArg subjectReductionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (subjectReduction_round_trip x).symm
      (Eq.trans hread (subjectReduction_round_trip y)))

instance subjectReductionBHistCarrier : BHistCarrier SubjectReductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := subjectReductionToEventFlow
  fromEventFlow := subjectReductionFromEventFlow

instance subjectReductionChapterTasteGate : ChapterTasteGate SubjectReductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change subjectReductionFromEventFlow (subjectReductionToEventFlow x) = some x
    exact subjectReduction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (subjectReductionToEventFlow_injective heq)

theorem SubjectReductionTasteGate_single_carrier_alignment :
    (∀ h : BHist, subjectReductionDecodeBHist (subjectReductionEncodeBHist h) = h) ∧
      (∀ x : SubjectReductionUp,
        subjectReductionFromEventFlow (subjectReductionToEventFlow x) = some x) ∧
        (∀ x y : SubjectReductionUp,
          subjectReductionToEventFlow x = subjectReductionToEventFlow y → x = y) ∧
          subjectReductionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact subjectReductionDecode_encode_bhist
  · constructor
    · exact subjectReduction_round_trip
    · constructor
      · intro x y heq
        exact subjectReductionToEventFlow_injective heq
      · rfl

end BEDC.Derived.SubjectReductionUp
