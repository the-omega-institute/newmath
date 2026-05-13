import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TypeCheckingDerivationTraceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TypeCheckingDerivationTraceUp : Type where
  | mk :
      (term classifier reductionRoute derivationLedger transport subjectReduction provenance
        localName : BHist) →
      TypeCheckingDerivationTraceUp
  deriving DecidableEq

private def typeCheckingDerivationTraceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: typeCheckingDerivationTraceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: typeCheckingDerivationTraceEncodeBHist h

private def typeCheckingDerivationTraceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (typeCheckingDerivationTraceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (typeCheckingDerivationTraceDecodeBHist tail)

private theorem typeCheckingDerivationTraceDecode_encode_bhist :
    ∀ h : BHist,
      typeCheckingDerivationTraceDecodeBHist (typeCheckingDerivationTraceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem typeCheckingDerivationTrace_mk_congr
    {term term' classifier classifier' reductionRoute reductionRoute'
      derivationLedger derivationLedger' transport transport'
      subjectReduction subjectReduction' provenance provenance' localName localName' : BHist}
    (hTerm : term' = term)
    (hClassifier : classifier' = classifier)
    (hReductionRoute : reductionRoute' = reductionRoute)
    (hDerivationLedger : derivationLedger' = derivationLedger)
    (hTransport : transport' = transport)
    (hSubjectReduction : subjectReduction' = subjectReduction)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    TypeCheckingDerivationTraceUp.mk term' classifier' reductionRoute' derivationLedger'
        transport' subjectReduction' provenance' localName' =
      TypeCheckingDerivationTraceUp.mk term classifier reductionRoute derivationLedger transport
        subjectReduction provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hTerm
  cases hClassifier
  cases hReductionRoute
  cases hDerivationLedger
  cases hTransport
  cases hSubjectReduction
  cases hProvenance
  cases hLocalName
  rfl

private def typeCheckingDerivationTraceToEventFlow :
    TypeCheckingDerivationTraceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TypeCheckingDerivationTraceUp.mk term classifier reductionRoute derivationLedger
      transport subjectReduction provenance localName =>
      [[BMark.b0],
        typeCheckingDerivationTraceEncodeBHist term,
        [BMark.b1, BMark.b0],
        typeCheckingDerivationTraceEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b0],
        typeCheckingDerivationTraceEncodeBHist reductionRoute,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        typeCheckingDerivationTraceEncodeBHist derivationLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        typeCheckingDerivationTraceEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        typeCheckingDerivationTraceEncodeBHist subjectReduction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        typeCheckingDerivationTraceEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        typeCheckingDerivationTraceEncodeBHist localName]

private def typeCheckingDerivationTraceFromEventFlow :
    EventFlow → Option TypeCheckingDerivationTraceUp
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
              | classifier :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | reductionRoute :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | derivationLedger :: rest7 =>
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
                                              | subjectReduction :: rest11 =>
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
                                                              | localName :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (TypeCheckingDerivationTraceUp.mk
                                                                          (typeCheckingDerivationTraceDecodeBHist term)
                                                                          (typeCheckingDerivationTraceDecodeBHist classifier)
                                                                          (typeCheckingDerivationTraceDecodeBHist reductionRoute)
                                                                          (typeCheckingDerivationTraceDecodeBHist derivationLedger)
                                                                          (typeCheckingDerivationTraceDecodeBHist transport)
                                                                          (typeCheckingDerivationTraceDecodeBHist subjectReduction)
                                                                          (typeCheckingDerivationTraceDecodeBHist provenance)
                                                                          (typeCheckingDerivationTraceDecodeBHist localName))
                                                                  | _ :: _ => none

private theorem typeCheckingDerivationTrace_round_trip :
    ∀ x : TypeCheckingDerivationTraceUp,
      typeCheckingDerivationTraceFromEventFlow (typeCheckingDerivationTraceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk term classifier reductionRoute derivationLedger transport subjectReduction provenance
      localName =>
      change
        some
          (TypeCheckingDerivationTraceUp.mk
            (typeCheckingDerivationTraceDecodeBHist
              (typeCheckingDerivationTraceEncodeBHist term))
            (typeCheckingDerivationTraceDecodeBHist
              (typeCheckingDerivationTraceEncodeBHist classifier))
            (typeCheckingDerivationTraceDecodeBHist
              (typeCheckingDerivationTraceEncodeBHist reductionRoute))
            (typeCheckingDerivationTraceDecodeBHist
              (typeCheckingDerivationTraceEncodeBHist derivationLedger))
            (typeCheckingDerivationTraceDecodeBHist
              (typeCheckingDerivationTraceEncodeBHist transport))
            (typeCheckingDerivationTraceDecodeBHist
              (typeCheckingDerivationTraceEncodeBHist subjectReduction))
            (typeCheckingDerivationTraceDecodeBHist
              (typeCheckingDerivationTraceEncodeBHist provenance))
            (typeCheckingDerivationTraceDecodeBHist
              (typeCheckingDerivationTraceEncodeBHist localName))) =
          some
            (TypeCheckingDerivationTraceUp.mk term classifier reductionRoute derivationLedger
              transport subjectReduction provenance localName)
      exact
        congrArg some
          (typeCheckingDerivationTrace_mk_congr
            (typeCheckingDerivationTraceDecode_encode_bhist term)
            (typeCheckingDerivationTraceDecode_encode_bhist classifier)
            (typeCheckingDerivationTraceDecode_encode_bhist reductionRoute)
            (typeCheckingDerivationTraceDecode_encode_bhist derivationLedger)
            (typeCheckingDerivationTraceDecode_encode_bhist transport)
            (typeCheckingDerivationTraceDecode_encode_bhist subjectReduction)
            (typeCheckingDerivationTraceDecode_encode_bhist provenance)
            (typeCheckingDerivationTraceDecode_encode_bhist localName))

private theorem typeCheckingDerivationTraceToEventFlow_injective
    {x y : TypeCheckingDerivationTraceUp} :
    typeCheckingDerivationTraceToEventFlow x = typeCheckingDerivationTraceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      typeCheckingDerivationTraceFromEventFlow (typeCheckingDerivationTraceToEventFlow x) =
        typeCheckingDerivationTraceFromEventFlow (typeCheckingDerivationTraceToEventFlow y) :=
    congrArg typeCheckingDerivationTraceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (typeCheckingDerivationTrace_round_trip x).symm
      (Eq.trans hread (typeCheckingDerivationTrace_round_trip y)))

instance typeCheckingDerivationTraceBHistCarrier :
    BHistCarrier TypeCheckingDerivationTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := typeCheckingDerivationTraceToEventFlow
  fromEventFlow := typeCheckingDerivationTraceFromEventFlow

instance typeCheckingDerivationTraceChapterTasteGate :
    ChapterTasteGate TypeCheckingDerivationTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      typeCheckingDerivationTraceFromEventFlow (typeCheckingDerivationTraceToEventFlow x) =
        some x
    exact typeCheckingDerivationTrace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (typeCheckingDerivationTraceToEventFlow_injective heq)

theorem TypeCheckingDerivationTraceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      typeCheckingDerivationTraceDecodeBHist (typeCheckingDerivationTraceEncodeBHist h) = h) ∧
      (∀ x : TypeCheckingDerivationTraceUp,
        typeCheckingDerivationTraceFromEventFlow (typeCheckingDerivationTraceToEventFlow x) =
          some x) ∧
        (∀ x y : TypeCheckingDerivationTraceUp,
          typeCheckingDerivationTraceToEventFlow x = typeCheckingDerivationTraceToEventFlow y →
            x = y) ∧
          typeCheckingDerivationTraceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact typeCheckingDerivationTraceDecode_encode_bhist
  · constructor
    · exact typeCheckingDerivationTrace_round_trip
    · constructor
      · intro x y heq
        exact typeCheckingDerivationTraceToEventFlow_injective heq
      · rfl

end BEDC.Derived.TypeCheckingDerivationTraceUp
