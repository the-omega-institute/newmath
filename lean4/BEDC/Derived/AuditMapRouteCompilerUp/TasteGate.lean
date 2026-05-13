import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AuditMapRouteCompilerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AuditMapRouteCompilerUp : Type where
  | mk :
      (event source recognizer gate theoremCode chapterCode metric cannotClaim ledger transport
        continuation provenance name : BHist) →
        AuditMapRouteCompilerUp
  deriving DecidableEq

def auditMapRouteCompilerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: auditMapRouteCompilerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: auditMapRouteCompilerEncodeBHist h

def auditMapRouteCompilerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (auditMapRouteCompilerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (auditMapRouteCompilerDecodeBHist tail)

private theorem auditMapRouteCompilerDecode_encode_bhist :
    ∀ h : BHist, auditMapRouteCompilerDecodeBHist (auditMapRouteCompilerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem auditMapRouteCompiler_mk_congr
    {event event' source source' recognizer recognizer' gate gate' theoremCode theoremCode'
      chapterCode chapterCode' metric metric' cannotClaim cannotClaim' ledger ledger'
      transport transport' continuation continuation' provenance provenance' name name' : BHist}
    (hEvent : event' = event)
    (hSource : source' = source)
    (hRecognizer : recognizer' = recognizer)
    (hGate : gate' = gate)
    (hTheoremCode : theoremCode' = theoremCode)
    (hChapterCode : chapterCode' = chapterCode)
    (hMetric : metric' = metric)
    (hCannotClaim : cannotClaim' = cannotClaim)
    (hLedger : ledger' = ledger)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    AuditMapRouteCompilerUp.mk event' source' recognizer' gate' theoremCode' chapterCode'
        metric' cannotClaim' ledger' transport' continuation' provenance' name' =
      AuditMapRouteCompilerUp.mk event source recognizer gate theoremCode chapterCode metric
        cannotClaim ledger transport continuation provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hEvent
  cases hSource
  cases hRecognizer
  cases hGate
  cases hTheoremCode
  cases hChapterCode
  cases hMetric
  cases hCannotClaim
  cases hLedger
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hName
  rfl

def auditMapRouteCompilerToEventFlow : AuditMapRouteCompilerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AuditMapRouteCompilerUp.mk event source recognizer gate theoremCode chapterCode metric
      cannotClaim ledger transport continuation provenance name =>
      [[BMark.b0],
        auditMapRouteCompilerEncodeBHist event,
        [BMark.b1, BMark.b0],
        auditMapRouteCompilerEncodeBHist source,
        [BMark.b1, BMark.b1, BMark.b0],
        auditMapRouteCompilerEncodeBHist recognizer,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapRouteCompilerEncodeBHist gate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapRouteCompilerEncodeBHist theoremCode,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapRouteCompilerEncodeBHist chapterCode,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapRouteCompilerEncodeBHist metric,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        auditMapRouteCompilerEncodeBHist cannotClaim,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        auditMapRouteCompilerEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        auditMapRouteCompilerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapRouteCompilerEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapRouteCompilerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapRouteCompilerEncodeBHist name]

def auditMapRouteCompilerFromEventFlow :
    EventFlow → Option AuditMapRouteCompilerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | event :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | source :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | recognizer :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | gate :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | theoremCode :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | chapterCode :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | metric :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | cannotClaim :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | ledger :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | transport :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | continuation :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] => none
                                                                                          | _tag11 :: rest22 =>
                                                                                              match rest22 with
                                                                                              | [] => none
                                                                                              | provenance :: rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] => none
                                                                                                  | _tag12 :: rest24 =>
                                                                                                      match rest24 with
                                                                                                      | [] => none
                                                                                                      | name :: rest25 =>
                                                                                                          match rest25 with
                                                                                                          | [] =>
                                                                                                              some
                                                                                                                (AuditMapRouteCompilerUp.mk
                                                                                                                  (auditMapRouteCompilerDecodeBHist event)
                                                                                                                  (auditMapRouteCompilerDecodeBHist source)
                                                                                                                  (auditMapRouteCompilerDecodeBHist recognizer)
                                                                                                                  (auditMapRouteCompilerDecodeBHist gate)
                                                                                                                  (auditMapRouteCompilerDecodeBHist theoremCode)
                                                                                                                  (auditMapRouteCompilerDecodeBHist chapterCode)
                                                                                                                  (auditMapRouteCompilerDecodeBHist metric)
                                                                                                                  (auditMapRouteCompilerDecodeBHist cannotClaim)
                                                                                                                  (auditMapRouteCompilerDecodeBHist ledger)
                                                                                                                  (auditMapRouteCompilerDecodeBHist transport)
                                                                                                                  (auditMapRouteCompilerDecodeBHist continuation)
                                                                                                                  (auditMapRouteCompilerDecodeBHist provenance)
                                                                                                                  (auditMapRouteCompilerDecodeBHist name))
                                                                                                          | _ :: _ => none

private theorem auditMapRouteCompiler_round_trip :
    ∀ x : AuditMapRouteCompilerUp,
      auditMapRouteCompilerFromEventFlow (auditMapRouteCompilerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk event source recognizer gate theoremCode chapterCode metric cannotClaim ledger transport
      continuation provenance name =>
      change
        some
          (AuditMapRouteCompilerUp.mk
            (auditMapRouteCompilerDecodeBHist (auditMapRouteCompilerEncodeBHist event))
            (auditMapRouteCompilerDecodeBHist (auditMapRouteCompilerEncodeBHist source))
            (auditMapRouteCompilerDecodeBHist (auditMapRouteCompilerEncodeBHist recognizer))
            (auditMapRouteCompilerDecodeBHist (auditMapRouteCompilerEncodeBHist gate))
            (auditMapRouteCompilerDecodeBHist (auditMapRouteCompilerEncodeBHist theoremCode))
            (auditMapRouteCompilerDecodeBHist (auditMapRouteCompilerEncodeBHist chapterCode))
            (auditMapRouteCompilerDecodeBHist (auditMapRouteCompilerEncodeBHist metric))
            (auditMapRouteCompilerDecodeBHist (auditMapRouteCompilerEncodeBHist cannotClaim))
            (auditMapRouteCompilerDecodeBHist (auditMapRouteCompilerEncodeBHist ledger))
            (auditMapRouteCompilerDecodeBHist (auditMapRouteCompilerEncodeBHist transport))
            (auditMapRouteCompilerDecodeBHist (auditMapRouteCompilerEncodeBHist continuation))
            (auditMapRouteCompilerDecodeBHist (auditMapRouteCompilerEncodeBHist provenance))
            (auditMapRouteCompilerDecodeBHist (auditMapRouteCompilerEncodeBHist name))) =
          some
            (AuditMapRouteCompilerUp.mk event source recognizer gate theoremCode chapterCode
              metric cannotClaim ledger transport continuation provenance name)
      exact
        congrArg some
          (auditMapRouteCompiler_mk_congr
            (auditMapRouteCompilerDecode_encode_bhist event)
            (auditMapRouteCompilerDecode_encode_bhist source)
            (auditMapRouteCompilerDecode_encode_bhist recognizer)
            (auditMapRouteCompilerDecode_encode_bhist gate)
            (auditMapRouteCompilerDecode_encode_bhist theoremCode)
            (auditMapRouteCompilerDecode_encode_bhist chapterCode)
            (auditMapRouteCompilerDecode_encode_bhist metric)
            (auditMapRouteCompilerDecode_encode_bhist cannotClaim)
            (auditMapRouteCompilerDecode_encode_bhist ledger)
            (auditMapRouteCompilerDecode_encode_bhist transport)
            (auditMapRouteCompilerDecode_encode_bhist continuation)
            (auditMapRouteCompilerDecode_encode_bhist provenance)
            (auditMapRouteCompilerDecode_encode_bhist name))

private theorem auditMapRouteCompilerToEventFlow_injective {x y : AuditMapRouteCompilerUp} :
    auditMapRouteCompilerToEventFlow x = auditMapRouteCompilerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      auditMapRouteCompilerFromEventFlow (auditMapRouteCompilerToEventFlow x) =
        auditMapRouteCompilerFromEventFlow (auditMapRouteCompilerToEventFlow y) :=
    congrArg auditMapRouteCompilerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (auditMapRouteCompiler_round_trip x).symm
      (Eq.trans hread (auditMapRouteCompiler_round_trip y)))

instance auditMapRouteCompilerBHistCarrier : BHistCarrier AuditMapRouteCompilerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := auditMapRouteCompilerToEventFlow
  fromEventFlow := auditMapRouteCompilerFromEventFlow

instance auditMapRouteCompilerChapterTasteGate :
    ChapterTasteGate AuditMapRouteCompilerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change auditMapRouteCompilerFromEventFlow (auditMapRouteCompilerToEventFlow x) = some x
    exact auditMapRouteCompiler_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (auditMapRouteCompilerToEventFlow_injective heq)

instance auditMapRouteCompilerFieldFaithful : FieldFaithful AuditMapRouteCompilerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | AuditMapRouteCompilerUp.mk event source recognizer gate theoremCode chapterCode metric
        cannotClaim ledger transport continuation provenance name =>
        [event, source, recognizer, gate, theoremCode, chapterCode, metric, cannotClaim,
          ledger, transport, continuation, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk event1 source1 recognizer1 gate1 theoremCode1 chapterCode1 metric1 cannotClaim1
        ledger1 transport1 continuation1 provenance1 name1 =>
        cases y with
        | mk event2 source2 recognizer2 gate2 theoremCode2 chapterCode2 metric2 cannotClaim2
            ledger2 transport2 continuation2 provenance2 name2 =>
            injection h with hEvent t1
            injection t1 with hSource t2
            injection t2 with hRecognizer t3
            injection t3 with hGate t4
            injection t4 with hTheoremCode t5
            injection t5 with hChapterCode t6
            injection t6 with hMetric t7
            injection t7 with hCannotClaim t8
            injection t8 with hLedger t9
            injection t9 with hTransport t10
            injection t10 with hContinuation t11
            injection t11 with hProvenance t12
            injection t12 with hName _
            cases hEvent
            cases hSource
            cases hRecognizer
            cases hGate
            cases hTheoremCode
            cases hChapterCode
            cases hMetric
            cases hCannotClaim
            cases hLedger
            cases hTransport
            cases hContinuation
            cases hProvenance
            cases hName
            rfl

instance auditMapRouteCompilerNontrivial : Nontrivial AuditMapRouteCompilerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AuditMapRouteCompilerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      AuditMapRouteCompilerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem AuditMapRouteCompilerTasteGate_single_carrier_alignment :
    (forall h : BHist,
        auditMapRouteCompilerDecodeBHist (auditMapRouteCompilerEncodeBHist h) = h) /\
      (forall x : AuditMapRouteCompilerUp,
        auditMapRouteCompilerFromEventFlow (auditMapRouteCompilerToEventFlow x) = some x) /\
      (forall x y : AuditMapRouteCompilerUp,
        auditMapRouteCompilerToEventFlow x = auditMapRouteCompilerToEventFlow y -> x = y) /\
      auditMapRouteCompilerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact auditMapRouteCompilerDecode_encode_bhist
  · constructor
    · exact auditMapRouteCompiler_round_trip
    · constructor
      · intro x y heq
        exact auditMapRouteCompilerToEventFlow_injective heq
      · rfl

end BEDC.Derived.AuditMapRouteCompilerUp
