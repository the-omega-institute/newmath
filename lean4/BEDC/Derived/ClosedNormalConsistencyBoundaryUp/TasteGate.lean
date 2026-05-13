import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

/-!
# ClosedNormalConsistencyBoundaryUp TasteGate carrier.
-/

namespace BEDC.Derived.ClosedNormalConsistencyBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Closed-normal consistency boundary packet with the ten displayed BEDC rows. -/
inductive ClosedNormalConsistencyBoundaryUp : Type where
  | mk :
      (typing closedness normality falseType positiveNode refusal transport continuation provenance
        nameCert : BHist) →
      ClosedNormalConsistencyBoundaryUp
  deriving DecidableEq

private def encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: encodeBHist h
  | BHist.e1 h => BMark.b1 :: encodeBHist h

private def decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (decodeBHist tail)

private theorem decode_encode_bhist : ∀ h : BHist, decodeBHist (encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def closedNormalConsistencyBoundaryToEventFlow :
    ClosedNormalConsistencyBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedNormalConsistencyBoundaryUp.mk typing closedness normality falseType positiveNode refusal
      transport continuation provenance nameCert =>
      [[BMark.b0],
        encodeBHist typing,
        [BMark.b1, BMark.b0],
        encodeBHist closedness,
        [BMark.b1, BMark.b1, BMark.b0],
        encodeBHist normality,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist falseType,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist positiveNode,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        encodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        encodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        encodeBHist nameCert]

private def closedNormalConsistencyBoundaryFromEventFlow :
    EventFlow → Option ClosedNormalConsistencyBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | typing :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | closedness :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | normality :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | falseType :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | positiveNode :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | refusal :: rest11 =>
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
                                                                              | nameCert :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (ClosedNormalConsistencyBoundaryUp.mk
                                                                                          (decodeBHist typing)
                                                                                          (decodeBHist closedness)
                                                                                          (decodeBHist normality)
                                                                                          (decodeBHist falseType)
                                                                                          (decodeBHist positiveNode)
                                                                                          (decodeBHist refusal)
                                                                                          (decodeBHist transport)
                                                                                          (decodeBHist continuation)
                                                                                          (decodeBHist provenance)
                                                                                          (decodeBHist nameCert))
                                                                                  | _ :: _ => none

private theorem closedNormalConsistencyBoundary_round_trip :
    ∀ x : ClosedNormalConsistencyBoundaryUp,
      closedNormalConsistencyBoundaryFromEventFlow
        (closedNormalConsistencyBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk typing closedness normality falseType positiveNode refusal transport continuation provenance
      nameCert =>
      change
        some
          (ClosedNormalConsistencyBoundaryUp.mk
            (decodeBHist (encodeBHist typing))
            (decodeBHist (encodeBHist closedness))
            (decodeBHist (encodeBHist normality))
            (decodeBHist (encodeBHist falseType))
            (decodeBHist (encodeBHist positiveNode))
            (decodeBHist (encodeBHist refusal))
            (decodeBHist (encodeBHist transport))
            (decodeBHist (encodeBHist continuation))
            (decodeBHist (encodeBHist provenance))
            (decodeBHist (encodeBHist nameCert))) =
          some
            (ClosedNormalConsistencyBoundaryUp.mk typing closedness normality falseType
              positiveNode refusal transport continuation provenance nameCert)
      rw [decode_encode_bhist typing, decode_encode_bhist closedness,
        decode_encode_bhist normality, decode_encode_bhist falseType,
        decode_encode_bhist positiveNode, decode_encode_bhist refusal,
        decode_encode_bhist transport, decode_encode_bhist continuation,
        decode_encode_bhist provenance, decode_encode_bhist nameCert]

private theorem closedNormalConsistencyBoundaryToEventFlow_injective
    {x y : ClosedNormalConsistencyBoundaryUp} :
    closedNormalConsistencyBoundaryToEventFlow x =
        closedNormalConsistencyBoundaryToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedNormalConsistencyBoundaryFromEventFlow
          (closedNormalConsistencyBoundaryToEventFlow x) =
        closedNormalConsistencyBoundaryFromEventFlow
          (closedNormalConsistencyBoundaryToEventFlow y) :=
    congrArg closedNormalConsistencyBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (closedNormalConsistencyBoundary_round_trip x).symm
      (Eq.trans hread (closedNormalConsistencyBoundary_round_trip y)))

instance closedNormalConsistencyBoundaryBHistCarrier :
    BHistCarrier ClosedNormalConsistencyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedNormalConsistencyBoundaryToEventFlow
  fromEventFlow := closedNormalConsistencyBoundaryFromEventFlow

instance closedNormalConsistencyBoundaryChapterTasteGate :
    ChapterTasteGate ClosedNormalConsistencyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedNormalConsistencyBoundaryFromEventFlow
          (closedNormalConsistencyBoundaryToEventFlow x) =
        some x
    exact closedNormalConsistencyBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closedNormalConsistencyBoundaryToEventFlow_injective heq)

theorem ClosedNormalConsistencyBoundaryUp_taste_gate_boundary :
    ∃ x : ClosedNormalConsistencyBoundaryUp,
      x =
          ClosedNormalConsistencyBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty ∧
        closedNormalConsistencyBoundaryFromEventFlow
            (closedNormalConsistencyBoundaryToEventFlow x) =
          some x := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨ClosedNormalConsistencyBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty, rfl, rfl⟩

end BEDC.Derived.ClosedNormalConsistencyBoundaryUp
