import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TypeCheckingDerivationTraceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TypeCheckingDerivationTraceUp : Type where
  | mk :
      (term classifier reductionRoute derivationLedger transport subjectReduction provenance
        localName : BHist) →
      TypeCheckingDerivationTraceUp
  deriving DecidableEq

def TypeCheckingDerivationTracePacket
    (term classifier reductionRoute derivationLedger transport subjectReduction provenance
      localName : BHist) : Prop :=
  UnaryHistory term ∧ UnaryHistory classifier ∧ UnaryHistory reductionRoute ∧
    UnaryHistory derivationLedger ∧ UnaryHistory transport ∧ UnaryHistory subjectReduction ∧
      UnaryHistory provenance ∧ UnaryHistory localName ∧ Cont term classifier reductionRoute ∧
        Cont reductionRoute derivationLedger transport ∧ Cont transport subjectReduction provenance

theorem TypeCheckingDerivationTracePacket_host_normalizer_nonescape
    {term classifier reductionRoute derivationLedger transport subjectReduction provenance
      localName : BHist} :
    TypeCheckingDerivationTracePacket term classifier reductionRoute derivationLedger transport
        subjectReduction provenance localName →
      UnaryHistory term ∧ UnaryHistory classifier ∧ Cont term classifier reductionRoute ∧
        Cont reductionRoute derivationLedger transport ∧ Cont transport subjectReduction provenance ∧
          hsame localName localName := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet
  cases packet with
  | intro termUnary rest =>
  cases rest with
  | intro classifierUnary rest =>
  cases rest with
  | intro _reductionRouteUnary rest =>
  cases rest with
  | intro _derivationLedgerUnary rest =>
  cases rest with
  | intro _transportUnary rest =>
  cases rest with
  | intro _subjectReductionUnary rest =>
  cases rest with
  | intro _provenanceUnary rest =>
  cases rest with
  | intro _localNameUnary rest =>
  cases rest with
  | intro termClassifierRoute rest =>
  cases rest with
  | intro reductionLedgerTransport transportSubjectProvenance =>
      exact
        And.intro termUnary
          (And.intro classifierUnary
            (And.intro termClassifierRoute
              (And.intro reductionLedgerTransport
                (And.intro transportSubjectProvenance (hsame_refl localName)))))

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

theorem TypeCheckingDerivationTracePacket_subject_reduction_transport
    {term classifier reductionRoute derivationLedger transport subjectReduction provenance
      localName term' classifier' reductionRoute' transport' provenance' : BHist} :
    TypeCheckingDerivationTracePacket term classifier reductionRoute derivationLedger transport
        subjectReduction provenance localName →
      hsame term term' →
        hsame classifier classifier' →
          Cont term' classifier' reductionRoute' →
            Cont reductionRoute' derivationLedger transport' →
              Cont transport' subjectReduction provenance' →
                TypeCheckingDerivationTracePacket term' classifier' reductionRoute' derivationLedger
                    transport' subjectReduction provenance' localName ∧
                  hsame reductionRoute reductionRoute' ∧
                    hsame transport transport' ∧ hsame provenance provenance' := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet sameTerm sameClassifier route' transportRoute' provenanceRoute'
  cases packet with
  | intro termUnary rest =>
  cases rest with
  | intro classifierUnary rest =>
  cases rest with
  | intro reductionRouteUnary rest =>
  cases rest with
  | intro derivationLedgerUnary rest =>
  cases rest with
  | intro transportUnary rest =>
  cases rest with
  | intro subjectReductionUnary rest =>
  cases rest with
  | intro provenanceUnary rest =>
  cases rest with
  | intro localNameUnary rest =>
  cases rest with
  | intro route rest =>
  cases rest with
  | intro transportRoute provenanceRoute =>
      have reductionRouteSame : hsame reductionRoute reductionRoute' :=
        cont_respects_hsame sameTerm sameClassifier route route'
      have transportSame : hsame transport transport' :=
        cont_respects_hsame reductionRouteSame (hsame_refl derivationLedger) transportRoute
          transportRoute'
      have provenanceSame : hsame provenance provenance' :=
        cont_respects_hsame transportSame (hsame_refl subjectReduction) provenanceRoute
          provenanceRoute'
      have termUnary' : UnaryHistory term' := unary_transport termUnary sameTerm
      have classifierUnary' : UnaryHistory classifier' :=
        unary_transport classifierUnary sameClassifier
      have reductionRouteUnary' : UnaryHistory reductionRoute' :=
        unary_transport reductionRouteUnary reductionRouteSame
      have transportUnary' : UnaryHistory transport' :=
        unary_transport transportUnary transportSame
      have provenanceUnary' : UnaryHistory provenance' :=
        unary_transport provenanceUnary provenanceSame
      exact
        And.intro
          (And.intro termUnary'
            (And.intro classifierUnary'
              (And.intro reductionRouteUnary'
                (And.intro derivationLedgerUnary
                  (And.intro transportUnary'
                    (And.intro subjectReductionUnary
                      (And.intro provenanceUnary'
                        (And.intro localNameUnary
                          (And.intro route'
                            (And.intro transportRoute' provenanceRoute'))))))))))
          (And.intro reductionRouteSame (And.intro transportSame provenanceSame))

end BEDC.Derived.TypeCheckingDerivationTraceUp
