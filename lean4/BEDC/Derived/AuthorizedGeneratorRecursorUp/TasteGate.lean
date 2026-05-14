import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AuthorizedGeneratorRecursorUp : Type where
  | mk :
      (signature eliminator motive branches descent output audit transport routes provenance gap
        name : BHist) →
      AuthorizedGeneratorRecursorUp
  deriving DecidableEq

def authorizedGeneratorRecursorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: authorizedGeneratorRecursorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: authorizedGeneratorRecursorEncodeBHist h

def authorizedGeneratorRecursorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (authorizedGeneratorRecursorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (authorizedGeneratorRecursorDecodeBHist tail)

private theorem authorizedGeneratorRecursorDecode_encode_bhist :
    ∀ h : BHist,
      authorizedGeneratorRecursorDecodeBHist (authorizedGeneratorRecursorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def authorizedGeneratorRecursorToEventFlow : AuthorizedGeneratorRecursorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output audit
      transport routes provenance gap name =>
      [[BMark.b0],
        authorizedGeneratorRecursorEncodeBHist signature,
        [BMark.b1, BMark.b0],
        authorizedGeneratorRecursorEncodeBHist eliminator,
        [BMark.b1, BMark.b1, BMark.b0],
        authorizedGeneratorRecursorEncodeBHist motive,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        authorizedGeneratorRecursorEncodeBHist branches,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        authorizedGeneratorRecursorEncodeBHist descent,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        authorizedGeneratorRecursorEncodeBHist output,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        authorizedGeneratorRecursorEncodeBHist audit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        authorizedGeneratorRecursorEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        authorizedGeneratorRecursorEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        authorizedGeneratorRecursorEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        authorizedGeneratorRecursorEncodeBHist gap,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        authorizedGeneratorRecursorEncodeBHist name]

def authorizedGeneratorRecursorFromEventFlow : EventFlow → Option AuthorizedGeneratorRecursorUp
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
              | eliminator :: rest3 =>
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
                                      | descent :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | output :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | audit :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | transport :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | routes ::
                                                                          rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match
                                                                                rest18
                                                                              with
                                                                              | [] =>
                                                                                  none
                                                                              | provenance ::
                                                                                  rest19 =>
                                                                                  match
                                                                                    rest19
                                                                                  with
                                                                                  | [] =>
                                                                                      none
                                                                                  | _tag10 ::
                                                                                      rest20 =>
                                                                                      match
                                                                                        rest20
                                                                                      with
                                                                                      | [] =>
                                                                                          none
                                                                                      | gap ::
                                                                                          rest21 =>
                                                                                          match
                                                                                            rest21
                                                                                          with
                                                                                          | [] =>
                                                                                              none
                                                                                          | _tag11 ::
                                                                                              rest22 =>
                                                                                              match
                                                                                                rest22
                                                                                              with
                                                                                              | [] =>
                                                                                                  none
                                                                                              | name ::
                                                                                                  rest23 =>
                                                                                                  match
                                                                                                    rest23
                                                                                                  with
                                                                                                  | [] =>
                                                                                                      some
                                                                                                        (AuthorizedGeneratorRecursorUp.mk
                                                                                                          (authorizedGeneratorRecursorDecodeBHist
                                                                                                            signature)
                                                                                                          (authorizedGeneratorRecursorDecodeBHist
                                                                                                            eliminator)
                                                                                                          (authorizedGeneratorRecursorDecodeBHist
                                                                                                            motive)
                                                                                                          (authorizedGeneratorRecursorDecodeBHist
                                                                                                            branches)
                                                                                                          (authorizedGeneratorRecursorDecodeBHist
                                                                                                            descent)
                                                                                                          (authorizedGeneratorRecursorDecodeBHist
                                                                                                            output)
                                                                                                          (authorizedGeneratorRecursorDecodeBHist
                                                                                                            audit)
                                                                                                          (authorizedGeneratorRecursorDecodeBHist
                                                                                                            transport)
                                                                                                          (authorizedGeneratorRecursorDecodeBHist
                                                                                                            routes)
                                                                                                          (authorizedGeneratorRecursorDecodeBHist
                                                                                                            provenance)
                                                                                                          (authorizedGeneratorRecursorDecodeBHist
                                                                                                            gap)
                                                                                                          (authorizedGeneratorRecursorDecodeBHist
                                                                                                            name))
                                                                                                  | _ :: _ =>
                                                                                                      none

private theorem authorizedGeneratorRecursor_round_trip :
    ∀ x : AuthorizedGeneratorRecursorUp,
      authorizedGeneratorRecursorFromEventFlow (authorizedGeneratorRecursorToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk signature eliminator motive branches descent output audit transport routes provenance gap
      name =>
      change
        some
          (AuthorizedGeneratorRecursorUp.mk
            (authorizedGeneratorRecursorDecodeBHist
              (authorizedGeneratorRecursorEncodeBHist signature))
            (authorizedGeneratorRecursorDecodeBHist
              (authorizedGeneratorRecursorEncodeBHist eliminator))
            (authorizedGeneratorRecursorDecodeBHist
              (authorizedGeneratorRecursorEncodeBHist motive))
            (authorizedGeneratorRecursorDecodeBHist
              (authorizedGeneratorRecursorEncodeBHist branches))
            (authorizedGeneratorRecursorDecodeBHist
              (authorizedGeneratorRecursorEncodeBHist descent))
            (authorizedGeneratorRecursorDecodeBHist
              (authorizedGeneratorRecursorEncodeBHist output))
            (authorizedGeneratorRecursorDecodeBHist
              (authorizedGeneratorRecursorEncodeBHist audit))
            (authorizedGeneratorRecursorDecodeBHist
              (authorizedGeneratorRecursorEncodeBHist transport))
            (authorizedGeneratorRecursorDecodeBHist
              (authorizedGeneratorRecursorEncodeBHist routes))
            (authorizedGeneratorRecursorDecodeBHist
              (authorizedGeneratorRecursorEncodeBHist provenance))
            (authorizedGeneratorRecursorDecodeBHist
              (authorizedGeneratorRecursorEncodeBHist gap))
            (authorizedGeneratorRecursorDecodeBHist
              (authorizedGeneratorRecursorEncodeBHist name))) =
          some
            (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output
              audit transport routes provenance gap name)
      rw [authorizedGeneratorRecursorDecode_encode_bhist signature,
        authorizedGeneratorRecursorDecode_encode_bhist eliminator,
        authorizedGeneratorRecursorDecode_encode_bhist motive,
        authorizedGeneratorRecursorDecode_encode_bhist branches,
        authorizedGeneratorRecursorDecode_encode_bhist descent,
        authorizedGeneratorRecursorDecode_encode_bhist output,
        authorizedGeneratorRecursorDecode_encode_bhist audit,
        authorizedGeneratorRecursorDecode_encode_bhist transport,
        authorizedGeneratorRecursorDecode_encode_bhist routes,
        authorizedGeneratorRecursorDecode_encode_bhist provenance,
        authorizedGeneratorRecursorDecode_encode_bhist gap,
        authorizedGeneratorRecursorDecode_encode_bhist name]

private theorem authorizedGeneratorRecursorToEventFlow_injective {x y : AuthorizedGeneratorRecursorUp} :
    authorizedGeneratorRecursorToEventFlow x = authorizedGeneratorRecursorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      authorizedGeneratorRecursorFromEventFlow (authorizedGeneratorRecursorToEventFlow x) =
        authorizedGeneratorRecursorFromEventFlow (authorizedGeneratorRecursorToEventFlow y) :=
    congrArg authorizedGeneratorRecursorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (authorizedGeneratorRecursor_round_trip x).symm
      (Eq.trans hread (authorizedGeneratorRecursor_round_trip y)))

instance authorizedGeneratorRecursorBHistCarrier : BHistCarrier AuthorizedGeneratorRecursorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := authorizedGeneratorRecursorToEventFlow
  fromEventFlow := authorizedGeneratorRecursorFromEventFlow

instance authorizedGeneratorRecursorChapterTasteGate :
    ChapterTasteGate AuthorizedGeneratorRecursorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      authorizedGeneratorRecursorFromEventFlow (authorizedGeneratorRecursorToEventFlow x) =
        some x
    exact authorizedGeneratorRecursor_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (authorizedGeneratorRecursorToEventFlow_injective heq)

def taste_gate : ChapterTasteGate AuthorizedGeneratorRecursorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  authorizedGeneratorRecursorChapterTasteGate

theorem AuthorizedGeneratorRecursorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        authorizedGeneratorRecursorDecodeBHist (authorizedGeneratorRecursorEncodeBHist h) = h) ∧
      (∀ x : AuthorizedGeneratorRecursorUp,
        authorizedGeneratorRecursorFromEventFlow (authorizedGeneratorRecursorToEventFlow x) =
          some x) ∧
        (∀ x y : AuthorizedGeneratorRecursorUp,
          authorizedGeneratorRecursorToEventFlow x =
            authorizedGeneratorRecursorToEventFlow y → x = y) ∧
          authorizedGeneratorRecursorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact authorizedGeneratorRecursorDecode_encode_bhist
  · constructor
    · exact authorizedGeneratorRecursor_round_trip
    · constructor
      · intro x y heq
        exact authorizedGeneratorRecursorToEventFlow_injective heq
      · rfl

end BEDC.Derived.AuthorizedGeneratorRecursorUp
