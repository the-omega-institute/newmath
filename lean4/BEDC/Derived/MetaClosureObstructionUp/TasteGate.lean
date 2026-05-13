import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaClosureObstructionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaClosureObstructionUp : Type where
  | mk :
      (refutation schema refusal truthBranch metaLoop transport continuations provenance
        nameCert : BHist) →
      MetaClosureObstructionUp
  deriving DecidableEq

def metaClosureObstructionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaClosureObstructionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaClosureObstructionEncodeBHist h

def metaClosureObstructionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaClosureObstructionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaClosureObstructionDecodeBHist tail)

private theorem metaClosureObstruction_decode_encode_bhist :
    ∀ h : BHist, metaClosureObstructionDecodeBHist (metaClosureObstructionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metaClosureObstructionToEventFlow : MetaClosureObstructionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetaClosureObstructionUp.mk refutation schema refusal truthBranch metaLoop transport
      continuations provenance nameCert =>
      [[BMark.b0],
        metaClosureObstructionEncodeBHist refutation,
        [BMark.b1, BMark.b0],
        metaClosureObstructionEncodeBHist schema,
        [BMark.b1, BMark.b1, BMark.b0],
        metaClosureObstructionEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaClosureObstructionEncodeBHist truthBranch,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaClosureObstructionEncodeBHist metaLoop,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaClosureObstructionEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaClosureObstructionEncodeBHist continuations,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metaClosureObstructionEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metaClosureObstructionEncodeBHist nameCert]

def metaClosureObstructionFromEventFlow : EventFlow → Option MetaClosureObstructionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | refutation :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | schema :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | refusal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | truthBranch :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | metaLoop :: rest9 =>
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
                                                      | continuations :: rest13 =>
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
                                                                      | nameCert :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (MetaClosureObstructionUp.mk
                                                                                  (metaClosureObstructionDecodeBHist
                                                                                    refutation)
                                                                                  (metaClosureObstructionDecodeBHist
                                                                                    schema)
                                                                                  (metaClosureObstructionDecodeBHist
                                                                                    refusal)
                                                                                  (metaClosureObstructionDecodeBHist
                                                                                    truthBranch)
                                                                                  (metaClosureObstructionDecodeBHist
                                                                                    metaLoop)
                                                                                  (metaClosureObstructionDecodeBHist
                                                                                    transport)
                                                                                  (metaClosureObstructionDecodeBHist
                                                                                    continuations)
                                                                                  (metaClosureObstructionDecodeBHist
                                                                                    provenance)
                                                                                  (metaClosureObstructionDecodeBHist
                                                                                    nameCert))
                                                                          | _ :: _ => none

private theorem metaClosureObstruction_mk_congr
    {refutation refutation' schema schema' refusal refusal' truthBranch truthBranch'
      metaLoop metaLoop' transport transport' continuations continuations' provenance provenance'
      nameCert nameCert' : BHist}
    (hRefutation : refutation' = refutation)
    (hSchema : schema' = schema)
    (hRefusal : refusal' = refusal)
    (hTruthBranch : truthBranch' = truthBranch)
    (hMetaLoop : metaLoop' = metaLoop)
    (hTransport : transport' = transport)
    (hContinuations : continuations' = continuations)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    MetaClosureObstructionUp.mk refutation' schema' refusal' truthBranch' metaLoop' transport'
        continuations' provenance' nameCert' =
      MetaClosureObstructionUp.mk refutation schema refusal truthBranch metaLoop transport
        continuations provenance nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hRefutation
  cases hSchema
  cases hRefusal
  cases hTruthBranch
  cases hMetaLoop
  cases hTransport
  cases hContinuations
  cases hProvenance
  cases hNameCert
  rfl

private theorem metaClosureObstruction_round_trip :
    ∀ x : MetaClosureObstructionUp,
      metaClosureObstructionFromEventFlow (metaClosureObstructionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk refutation schema refusal truthBranch metaLoop transport continuations provenance nameCert =>
      change
        some
          (MetaClosureObstructionUp.mk
            (metaClosureObstructionDecodeBHist (metaClosureObstructionEncodeBHist refutation))
            (metaClosureObstructionDecodeBHist (metaClosureObstructionEncodeBHist schema))
            (metaClosureObstructionDecodeBHist (metaClosureObstructionEncodeBHist refusal))
            (metaClosureObstructionDecodeBHist (metaClosureObstructionEncodeBHist truthBranch))
            (metaClosureObstructionDecodeBHist (metaClosureObstructionEncodeBHist metaLoop))
            (metaClosureObstructionDecodeBHist (metaClosureObstructionEncodeBHist transport))
            (metaClosureObstructionDecodeBHist (metaClosureObstructionEncodeBHist continuations))
            (metaClosureObstructionDecodeBHist (metaClosureObstructionEncodeBHist provenance))
            (metaClosureObstructionDecodeBHist (metaClosureObstructionEncodeBHist nameCert))) =
          some
            (MetaClosureObstructionUp.mk refutation schema refusal truthBranch metaLoop transport
              continuations provenance nameCert)
      exact
        congrArg some
          (metaClosureObstruction_mk_congr
            (metaClosureObstruction_decode_encode_bhist refutation)
            (metaClosureObstruction_decode_encode_bhist schema)
            (metaClosureObstruction_decode_encode_bhist refusal)
            (metaClosureObstruction_decode_encode_bhist truthBranch)
            (metaClosureObstruction_decode_encode_bhist metaLoop)
            (metaClosureObstruction_decode_encode_bhist transport)
            (metaClosureObstruction_decode_encode_bhist continuations)
            (metaClosureObstruction_decode_encode_bhist provenance)
            (metaClosureObstruction_decode_encode_bhist nameCert))

private theorem metaClosureObstructionToEventFlow_injective {x y : MetaClosureObstructionUp} :
    metaClosureObstructionToEventFlow x = metaClosureObstructionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaClosureObstructionFromEventFlow (metaClosureObstructionToEventFlow x) =
        metaClosureObstructionFromEventFlow (metaClosureObstructionToEventFlow y) :=
    congrArg metaClosureObstructionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaClosureObstruction_round_trip x).symm
      (Eq.trans hread (metaClosureObstruction_round_trip y)))

instance metaClosureObstructionBHistCarrier : BHistCarrier MetaClosureObstructionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaClosureObstructionToEventFlow
  fromEventFlow := metaClosureObstructionFromEventFlow

instance metaClosureObstructionChapterTasteGate :
    ChapterTasteGate MetaClosureObstructionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metaClosureObstructionFromEventFlow (metaClosureObstructionToEventFlow x) = some x
    exact metaClosureObstruction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaClosureObstructionToEventFlow_injective heq)

instance metaClosureObstructionFieldFaithful : FieldFaithful MetaClosureObstructionUp where
  fields
    | MetaClosureObstructionUp.mk refutation schema refusal truthBranch metaLoop transport
        continuations provenance nameCert =>
        [refutation, schema, refusal, truthBranch, metaLoop, transport, continuations,
          provenance, nameCert]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y hfields
    cases x with
    | mk refutation schema refusal truthBranch metaLoop transport continuations provenance
        nameCert =>
        cases y with
        | mk refutation' schema' refusal' truthBranch' metaLoop' transport' continuations'
            provenance' nameCert' =>
            cases hfields
            rfl

theorem MetaClosureObstructionTasteGate_single_carrier_alignment :
    (∀ h : BHist, metaClosureObstructionDecodeBHist (metaClosureObstructionEncodeBHist h) = h) ∧
      (∀ x : MetaClosureObstructionUp,
        metaClosureObstructionFromEventFlow (metaClosureObstructionToEventFlow x) = some x) ∧
        (∀ x y : MetaClosureObstructionUp,
          metaClosureObstructionToEventFlow x = metaClosureObstructionToEventFlow y → x = y) ∧
          metaClosureObstructionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact metaClosureObstruction_decode_encode_bhist
  · constructor
    · exact metaClosureObstruction_round_trip
    · constructor
      · intro x y heq
        exact metaClosureObstructionToEventFlow_injective heq
      · rfl

end BEDC.Derived.MetaClosureObstructionUp
