import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICOpenProblemWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICOpenProblemWitnessUp : Type where
  | mk :
      (subjectReduction confluence normalization decidability typedExamples consistencyFrontier
        transport route provenance localName : BHist) →
      MetaCICOpenProblemWitnessUp
  deriving DecidableEq

def metaCICOpenProblemWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICOpenProblemWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICOpenProblemWitnessEncodeBHist h

def metaCICOpenProblemWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICOpenProblemWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICOpenProblemWitnessDecodeBHist tail)

private theorem metaCICOpenProblemWitnessDecode_encode_bhist :
    ∀ h : BHist,
      metaCICOpenProblemWitnessDecodeBHist (metaCICOpenProblemWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metaCICOpenProblemWitnessFields : MetaCICOpenProblemWitnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICOpenProblemWitnessUp.mk subjectReduction confluence normalization decidability
      typedExamples consistencyFrontier transport route provenance localName =>
      [subjectReduction, confluence, normalization, decidability, typedExamples,
        consistencyFrontier, transport, route, provenance, localName]

def metaCICOpenProblemWitnessToEventFlow : MetaCICOpenProblemWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICOpenProblemWitnessUp.mk subjectReduction confluence normalization decidability
      typedExamples consistencyFrontier transport route provenance localName =>
      [[BMark.b0],
        metaCICOpenProblemWitnessEncodeBHist subjectReduction,
        [BMark.b1, BMark.b0],
        metaCICOpenProblemWitnessEncodeBHist confluence,
        [BMark.b1, BMark.b1, BMark.b0],
        metaCICOpenProblemWitnessEncodeBHist normalization,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICOpenProblemWitnessEncodeBHist decidability,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICOpenProblemWitnessEncodeBHist typedExamples,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICOpenProblemWitnessEncodeBHist consistencyFrontier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICOpenProblemWitnessEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metaCICOpenProblemWitnessEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metaCICOpenProblemWitnessEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        metaCICOpenProblemWitnessEncodeBHist localName]

def metaCICOpenProblemWitnessFromEventFlow :
    EventFlow → Option MetaCICOpenProblemWitnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | subjectReduction :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | confluence :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | normalization :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | decidability :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | typedExamples :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | consistencyFrontier :: rest11 =>
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
                                                              | route :: rest15 =>
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
                                                                              match rest18
                                                                                with
                                                                              | [] => none
                                                                              | localName ::
                                                                                  rest19 =>
                                                                                  match rest19
                                                                                    with
                                                                                  | [] =>
                                                                                      some
                                                                                        (MetaCICOpenProblemWitnessUp.mk
                                                                                          (metaCICOpenProblemWitnessDecodeBHist
                                                                                            subjectReduction)
                                                                                          (metaCICOpenProblemWitnessDecodeBHist
                                                                                            confluence)
                                                                                          (metaCICOpenProblemWitnessDecodeBHist
                                                                                            normalization)
                                                                                          (metaCICOpenProblemWitnessDecodeBHist
                                                                                            decidability)
                                                                                          (metaCICOpenProblemWitnessDecodeBHist
                                                                                            typedExamples)
                                                                                          (metaCICOpenProblemWitnessDecodeBHist
                                                                                            consistencyFrontier)
                                                                                          (metaCICOpenProblemWitnessDecodeBHist
                                                                                            transport)
                                                                                          (metaCICOpenProblemWitnessDecodeBHist
                                                                                            route)
                                                                                          (metaCICOpenProblemWitnessDecodeBHist
                                                                                            provenance)
                                                                                          (metaCICOpenProblemWitnessDecodeBHist
                                                                                            localName))
                                                                                  | _ :: _ =>
                                                                                      none

private theorem metaCICOpenProblemWitness_round_trip :
    ∀ x : MetaCICOpenProblemWitnessUp,
      metaCICOpenProblemWitnessFromEventFlow (metaCICOpenProblemWitnessToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk subjectReduction confluence normalization decidability typedExamples consistencyFrontier
      transport route provenance localName =>
      change
        some
          (MetaCICOpenProblemWitnessUp.mk
            (metaCICOpenProblemWitnessDecodeBHist
              (metaCICOpenProblemWitnessEncodeBHist subjectReduction))
            (metaCICOpenProblemWitnessDecodeBHist
              (metaCICOpenProblemWitnessEncodeBHist confluence))
            (metaCICOpenProblemWitnessDecodeBHist
              (metaCICOpenProblemWitnessEncodeBHist normalization))
            (metaCICOpenProblemWitnessDecodeBHist
              (metaCICOpenProblemWitnessEncodeBHist decidability))
            (metaCICOpenProblemWitnessDecodeBHist
              (metaCICOpenProblemWitnessEncodeBHist typedExamples))
            (metaCICOpenProblemWitnessDecodeBHist
              (metaCICOpenProblemWitnessEncodeBHist consistencyFrontier))
            (metaCICOpenProblemWitnessDecodeBHist
              (metaCICOpenProblemWitnessEncodeBHist transport))
            (metaCICOpenProblemWitnessDecodeBHist
              (metaCICOpenProblemWitnessEncodeBHist route))
            (metaCICOpenProblemWitnessDecodeBHist
              (metaCICOpenProblemWitnessEncodeBHist provenance))
            (metaCICOpenProblemWitnessDecodeBHist
              (metaCICOpenProblemWitnessEncodeBHist localName))) =
          some
            (MetaCICOpenProblemWitnessUp.mk subjectReduction confluence normalization
              decidability typedExamples consistencyFrontier transport route provenance localName)
      rw [metaCICOpenProblemWitnessDecode_encode_bhist subjectReduction,
        metaCICOpenProblemWitnessDecode_encode_bhist confluence,
        metaCICOpenProblemWitnessDecode_encode_bhist normalization,
        metaCICOpenProblemWitnessDecode_encode_bhist decidability,
        metaCICOpenProblemWitnessDecode_encode_bhist typedExamples,
        metaCICOpenProblemWitnessDecode_encode_bhist consistencyFrontier,
        metaCICOpenProblemWitnessDecode_encode_bhist transport,
        metaCICOpenProblemWitnessDecode_encode_bhist route,
        metaCICOpenProblemWitnessDecode_encode_bhist provenance,
        metaCICOpenProblemWitnessDecode_encode_bhist localName]

private theorem metaCICOpenProblemWitnessToEventFlow_injective
    {x y : MetaCICOpenProblemWitnessUp} :
    metaCICOpenProblemWitnessToEventFlow x = metaCICOpenProblemWitnessToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICOpenProblemWitnessFromEventFlow (metaCICOpenProblemWitnessToEventFlow x) =
        metaCICOpenProblemWitnessFromEventFlow (metaCICOpenProblemWitnessToEventFlow y) :=
    congrArg metaCICOpenProblemWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaCICOpenProblemWitness_round_trip x).symm
      (Eq.trans hread (metaCICOpenProblemWitness_round_trip y)))

private theorem MetaCICOpenProblemWitnessTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : MetaCICOpenProblemWitnessUp,
      metaCICOpenProblemWitnessFields x = metaCICOpenProblemWitnessFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk subjectReduction confluence normalization decidability typedExamples consistencyFrontier
      transport route provenance localName =>
      cases y with
      | mk subjectReduction' confluence' normalization' decidability' typedExamples'
          consistencyFrontier' transport' route' provenance' localName' =>
          injection hfields with hSubjectReduction hTail0
          injection hTail0 with hConfluence hTail1
          injection hTail1 with hNormalization hTail2
          injection hTail2 with hDecidability hTail3
          injection hTail3 with hTypedExamples hTail4
          injection hTail4 with hConsistencyFrontier hTail5
          injection hTail5 with hTransport hTail6
          injection hTail6 with hRoute hTail7
          injection hTail7 with hProvenance hTail8
          injection hTail8 with hLocalName _hNil
          cases hSubjectReduction
          cases hConfluence
          cases hNormalization
          cases hDecidability
          cases hTypedExamples
          cases hConsistencyFrontier
          cases hTransport
          cases hRoute
          cases hProvenance
          cases hLocalName
          rfl

instance metaCICOpenProblemWitnessBHistCarrier : BHistCarrier MetaCICOpenProblemWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICOpenProblemWitnessToEventFlow
  fromEventFlow := metaCICOpenProblemWitnessFromEventFlow

instance metaCICOpenProblemWitnessChapterTasteGate :
    ChapterTasteGate MetaCICOpenProblemWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICOpenProblemWitnessFromEventFlow (metaCICOpenProblemWitnessToEventFlow x) =
        some x
    exact metaCICOpenProblemWitness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICOpenProblemWitnessToEventFlow_injective heq)

instance metaCICOpenProblemWitnessFieldFaithful :
    FieldFaithful MetaCICOpenProblemWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaCICOpenProblemWitnessFields
  field_faithful := MetaCICOpenProblemWitnessTasteGate_single_carrier_alignment_field_faithful

instance metaCICOpenProblemWitnessNontrivial : Nontrivial MetaCICOpenProblemWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICOpenProblemWitnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaCICOpenProblemWitnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetaCICOpenProblemWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICOpenProblemWitnessChapterTasteGate

theorem MetaCICOpenProblemWitnessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        metaCICOpenProblemWitnessDecodeBHist (metaCICOpenProblemWitnessEncodeBHist h) = h) ∧
      (∀ x : MetaCICOpenProblemWitnessUp,
        metaCICOpenProblemWitnessFromEventFlow (metaCICOpenProblemWitnessToEventFlow x) =
          some x) ∧
        (∀ x y : MetaCICOpenProblemWitnessUp,
          metaCICOpenProblemWitnessToEventFlow x = metaCICOpenProblemWitnessToEventFlow y →
            x = y) ∧
          metaCICOpenProblemWitnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨metaCICOpenProblemWitnessDecode_encode_bhist,
      metaCICOpenProblemWitness_round_trip,
      (by
        intro x y heq
        exact metaCICOpenProblemWitnessToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MetaCICOpenProblemWitnessUp
