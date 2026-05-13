import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ForbiddenAxiomAncestryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ForbiddenAxiomAncestryUp : Type where
  | mk :
      (theoremRow ancestry forbidden verdict transport routes provenance name : BHist) →
        ForbiddenAxiomAncestryUp
  deriving DecidableEq

def forbiddenAxiomAncestryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: forbiddenAxiomAncestryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: forbiddenAxiomAncestryEncodeBHist h

def forbiddenAxiomAncestryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (forbiddenAxiomAncestryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (forbiddenAxiomAncestryDecodeBHist tail)

private theorem forbiddenAxiomAncestryDecode_encode_bhist :
    ∀ h : BHist,
      forbiddenAxiomAncestryDecodeBHist (forbiddenAxiomAncestryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem forbiddenAxiomAncestry_mk_congr
    {theoremRow theoremRow' ancestry ancestry' forbidden forbidden' verdict verdict'
      transport transport' routes routes' provenance provenance' name name' : BHist}
    (hTheoremRow : theoremRow' = theoremRow)
    (hAncestry : ancestry' = ancestry)
    (hForbidden : forbidden' = forbidden)
    (hVerdict : verdict' = verdict)
    (hTransport : transport' = transport)
    (hRoutes : routes' = routes)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    ForbiddenAxiomAncestryUp.mk theoremRow' ancestry' forbidden' verdict' transport'
        routes' provenance' name' =
      ForbiddenAxiomAncestryUp.mk theoremRow ancestry forbidden verdict transport routes
        provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hTheoremRow
  cases hAncestry
  cases hForbidden
  cases hVerdict
  cases hTransport
  cases hRoutes
  cases hProvenance
  cases hName
  rfl

def forbiddenAxiomAncestryToEventFlow : ForbiddenAxiomAncestryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ForbiddenAxiomAncestryUp.mk theoremRow ancestry forbidden verdict transport routes
      provenance name =>
      [[BMark.b0],
        forbiddenAxiomAncestryEncodeBHist theoremRow,
        [BMark.b1, BMark.b0],
        forbiddenAxiomAncestryEncodeBHist ancestry,
        [BMark.b1, BMark.b1, BMark.b0],
        forbiddenAxiomAncestryEncodeBHist forbidden,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        forbiddenAxiomAncestryEncodeBHist verdict,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        forbiddenAxiomAncestryEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        forbiddenAxiomAncestryEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        forbiddenAxiomAncestryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        forbiddenAxiomAncestryEncodeBHist name]

def forbiddenAxiomAncestryFromEventFlow :
    EventFlow → Option ForbiddenAxiomAncestryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | theoremRow :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | ancestry :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | forbidden :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | verdict :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | routes :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | name :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (ForbiddenAxiomAncestryUp.mk
                                                                          (forbiddenAxiomAncestryDecodeBHist theoremRow)
                                                                          (forbiddenAxiomAncestryDecodeBHist ancestry)
                                                                          (forbiddenAxiomAncestryDecodeBHist forbidden)
                                                                          (forbiddenAxiomAncestryDecodeBHist verdict)
                                                                          (forbiddenAxiomAncestryDecodeBHist transport)
                                                                          (forbiddenAxiomAncestryDecodeBHist routes)
                                                                          (forbiddenAxiomAncestryDecodeBHist provenance)
                                                                          (forbiddenAxiomAncestryDecodeBHist name))
                                                                  | _ :: _ => none

private theorem forbiddenAxiomAncestry_round_trip :
    ∀ x : ForbiddenAxiomAncestryUp,
      forbiddenAxiomAncestryFromEventFlow
        (forbiddenAxiomAncestryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk theoremRow ancestry forbidden verdict transport routes provenance name =>
      change
        some
          (ForbiddenAxiomAncestryUp.mk
            (forbiddenAxiomAncestryDecodeBHist
              (forbiddenAxiomAncestryEncodeBHist theoremRow))
            (forbiddenAxiomAncestryDecodeBHist
              (forbiddenAxiomAncestryEncodeBHist ancestry))
            (forbiddenAxiomAncestryDecodeBHist
              (forbiddenAxiomAncestryEncodeBHist forbidden))
            (forbiddenAxiomAncestryDecodeBHist
              (forbiddenAxiomAncestryEncodeBHist verdict))
            (forbiddenAxiomAncestryDecodeBHist
              (forbiddenAxiomAncestryEncodeBHist transport))
            (forbiddenAxiomAncestryDecodeBHist
              (forbiddenAxiomAncestryEncodeBHist routes))
            (forbiddenAxiomAncestryDecodeBHist
              (forbiddenAxiomAncestryEncodeBHist provenance))
            (forbiddenAxiomAncestryDecodeBHist
              (forbiddenAxiomAncestryEncodeBHist name))) =
          some
            (ForbiddenAxiomAncestryUp.mk theoremRow ancestry forbidden verdict transport
              routes provenance name)
      exact
        congrArg some
          (forbiddenAxiomAncestry_mk_congr
            (forbiddenAxiomAncestryDecode_encode_bhist theoremRow)
            (forbiddenAxiomAncestryDecode_encode_bhist ancestry)
            (forbiddenAxiomAncestryDecode_encode_bhist forbidden)
            (forbiddenAxiomAncestryDecode_encode_bhist verdict)
            (forbiddenAxiomAncestryDecode_encode_bhist transport)
            (forbiddenAxiomAncestryDecode_encode_bhist routes)
            (forbiddenAxiomAncestryDecode_encode_bhist provenance)
            (forbiddenAxiomAncestryDecode_encode_bhist name))

private theorem forbiddenAxiomAncestryToEventFlow_injective
    {x y : ForbiddenAxiomAncestryUp} :
    forbiddenAxiomAncestryToEventFlow x =
      forbiddenAxiomAncestryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      forbiddenAxiomAncestryFromEventFlow
          (forbiddenAxiomAncestryToEventFlow x) =
        forbiddenAxiomAncestryFromEventFlow
          (forbiddenAxiomAncestryToEventFlow y) :=
    congrArg forbiddenAxiomAncestryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (forbiddenAxiomAncestry_round_trip x).symm
      (Eq.trans hread (forbiddenAxiomAncestry_round_trip y)))

instance forbiddenAxiomAncestryBHistCarrier :
    BHistCarrier ForbiddenAxiomAncestryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := forbiddenAxiomAncestryToEventFlow
  fromEventFlow := forbiddenAxiomAncestryFromEventFlow

instance forbiddenAxiomAncestryChapterTasteGate :
    ChapterTasteGate ForbiddenAxiomAncestryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      forbiddenAxiomAncestryFromEventFlow
        (forbiddenAxiomAncestryToEventFlow x) = some x
    exact forbiddenAxiomAncestry_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (forbiddenAxiomAncestryToEventFlow_injective heq)

theorem ForbiddenAxiomAncestryTasteGate_single_carrier_alignment :
    forbiddenAxiomAncestryEncodeBHist BHist.Empty = [] /\
      forbiddenAxiomAncestryEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] /\
      (forall h : BHist,
        forbiddenAxiomAncestryDecodeBHist
          (forbiddenAxiomAncestryEncodeBHist h) = h) /\
      (forall x : ForbiddenAxiomAncestryUp,
        forbiddenAxiomAncestryFromEventFlow
          (forbiddenAxiomAncestryToEventFlow x) = some x) /\
      (forall x y : ForbiddenAxiomAncestryUp,
        forbiddenAxiomAncestryToEventFlow x =
          forbiddenAxiomAncestryToEventFlow y -> x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · exact forbiddenAxiomAncestryDecode_encode_bhist
      · constructor
        · exact forbiddenAxiomAncestry_round_trip
        · intro x y heq
          exact forbiddenAxiomAncestryToEventFlow_injective heq

end BEDC.Derived.ForbiddenAxiomAncestryUp
