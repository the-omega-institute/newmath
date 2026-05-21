import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteTraceGapSocketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteTraceGapSocketUp : Type where
  | mk :
      (trace socket streamSchedule regseqReadback realSeal transports continuations provenance
        nameCert : BHist) →
      FiniteTraceGapSocketUp
  deriving DecidableEq

def finiteTraceGapSocketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteTraceGapSocketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteTraceGapSocketEncodeBHist h

def finiteTraceGapSocketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteTraceGapSocketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteTraceGapSocketDecodeBHist tail)

private theorem finiteTraceGapSocket_decode_encode_bhist :
    ∀ h : BHist, finiteTraceGapSocketDecodeBHist (finiteTraceGapSocketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteTraceGapSocketToEventFlow : FiniteTraceGapSocketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteTraceGapSocketUp.mk trace socket streamSchedule regseqReadback realSeal transports
      continuations provenance nameCert =>
      [[BMark.b0],
        finiteTraceGapSocketEncodeBHist trace,
        [BMark.b1, BMark.b0],
        finiteTraceGapSocketEncodeBHist socket,
        [BMark.b1, BMark.b1, BMark.b0],
        finiteTraceGapSocketEncodeBHist streamSchedule,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteTraceGapSocketEncodeBHist regseqReadback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteTraceGapSocketEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteTraceGapSocketEncodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteTraceGapSocketEncodeBHist continuations,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        finiteTraceGapSocketEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        finiteTraceGapSocketEncodeBHist nameCert]

def finiteTraceGapSocketFromEventFlow : EventFlow → Option FiniteTraceGapSocketUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | trace :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | socket :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | streamSchedule :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | regseqReadback :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | realSeal :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transports :: rest11 =>
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
                                                                                (FiniteTraceGapSocketUp.mk
                                                                                  (finiteTraceGapSocketDecodeBHist
                                                                                    trace)
                                                                                  (finiteTraceGapSocketDecodeBHist
                                                                                    socket)
                                                                                  (finiteTraceGapSocketDecodeBHist
                                                                                    streamSchedule)
                                                                                  (finiteTraceGapSocketDecodeBHist
                                                                                    regseqReadback)
                                                                                  (finiteTraceGapSocketDecodeBHist
                                                                                    realSeal)
                                                                                  (finiteTraceGapSocketDecodeBHist
                                                                                    transports)
                                                                                  (finiteTraceGapSocketDecodeBHist
                                                                                    continuations)
                                                                                  (finiteTraceGapSocketDecodeBHist
                                                                                    provenance)
                                                                                  (finiteTraceGapSocketDecodeBHist
                                                                                    nameCert))
                                                                          | _ :: _ => none

private theorem finiteTraceGapSocket_mk_congr
    {trace trace' socket socket' streamSchedule streamSchedule' regseqReadback
      regseqReadback' realSeal realSeal' transports transports' continuations continuations'
      provenance provenance' nameCert nameCert' : BHist}
    (hTrace : trace' = trace)
    (hSocket : socket' = socket)
    (hStreamSchedule : streamSchedule' = streamSchedule)
    (hRegseqReadback : regseqReadback' = regseqReadback)
    (hRealSeal : realSeal' = realSeal)
    (hTransports : transports' = transports)
    (hContinuations : continuations' = continuations)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    FiniteTraceGapSocketUp.mk trace' socket' streamSchedule' regseqReadback' realSeal'
        transports' continuations' provenance' nameCert' =
      FiniteTraceGapSocketUp.mk trace socket streamSchedule regseqReadback realSeal transports
        continuations provenance nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hTrace
  cases hSocket
  cases hStreamSchedule
  cases hRegseqReadback
  cases hRealSeal
  cases hTransports
  cases hContinuations
  cases hProvenance
  cases hNameCert
  rfl

private theorem finiteTraceGapSocket_round_trip :
    ∀ x : FiniteTraceGapSocketUp,
      finiteTraceGapSocketFromEventFlow (finiteTraceGapSocketToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk trace socket streamSchedule regseqReadback realSeal transports continuations provenance
      nameCert =>
      change
        some
          (FiniteTraceGapSocketUp.mk
            (finiteTraceGapSocketDecodeBHist (finiteTraceGapSocketEncodeBHist trace))
            (finiteTraceGapSocketDecodeBHist (finiteTraceGapSocketEncodeBHist socket))
            (finiteTraceGapSocketDecodeBHist (finiteTraceGapSocketEncodeBHist streamSchedule))
            (finiteTraceGapSocketDecodeBHist (finiteTraceGapSocketEncodeBHist regseqReadback))
            (finiteTraceGapSocketDecodeBHist (finiteTraceGapSocketEncodeBHist realSeal))
            (finiteTraceGapSocketDecodeBHist (finiteTraceGapSocketEncodeBHist transports))
            (finiteTraceGapSocketDecodeBHist (finiteTraceGapSocketEncodeBHist continuations))
            (finiteTraceGapSocketDecodeBHist (finiteTraceGapSocketEncodeBHist provenance))
            (finiteTraceGapSocketDecodeBHist (finiteTraceGapSocketEncodeBHist nameCert))) =
          some
            (FiniteTraceGapSocketUp.mk trace socket streamSchedule regseqReadback realSeal
              transports continuations provenance nameCert)
      exact
        congrArg some
          (finiteTraceGapSocket_mk_congr
            (finiteTraceGapSocket_decode_encode_bhist trace)
            (finiteTraceGapSocket_decode_encode_bhist socket)
            (finiteTraceGapSocket_decode_encode_bhist streamSchedule)
            (finiteTraceGapSocket_decode_encode_bhist regseqReadback)
            (finiteTraceGapSocket_decode_encode_bhist realSeal)
            (finiteTraceGapSocket_decode_encode_bhist transports)
            (finiteTraceGapSocket_decode_encode_bhist continuations)
            (finiteTraceGapSocket_decode_encode_bhist provenance)
            (finiteTraceGapSocket_decode_encode_bhist nameCert))

private theorem finiteTraceGapSocketToEventFlow_injective {x y : FiniteTraceGapSocketUp} :
    finiteTraceGapSocketToEventFlow x = finiteTraceGapSocketToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteTraceGapSocketFromEventFlow (finiteTraceGapSocketToEventFlow x) =
        finiteTraceGapSocketFromEventFlow (finiteTraceGapSocketToEventFlow y) :=
    congrArg finiteTraceGapSocketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteTraceGapSocket_round_trip x).symm
      (Eq.trans hread (finiteTraceGapSocket_round_trip y)))

instance finiteTraceGapSocketBHistCarrier : BHistCarrier FiniteTraceGapSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteTraceGapSocketToEventFlow
  fromEventFlow := finiteTraceGapSocketFromEventFlow

instance finiteTraceGapSocketChapterTasteGate :
    ChapterTasteGate FiniteTraceGapSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteTraceGapSocketFromEventFlow (finiteTraceGapSocketToEventFlow x) = some x
    exact finiteTraceGapSocket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteTraceGapSocketToEventFlow_injective heq)

instance finiteTraceGapSocketFieldFaithful : FieldFaithful FiniteTraceGapSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | FiniteTraceGapSocketUp.mk trace socket streamSchedule regseqReadback realSeal transports
        continuations provenance nameCert =>
        [trace, socket, streamSchedule, regseqReadback, realSeal, transports, continuations,
          provenance, nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk trace₁ socket₁ streamSchedule₁ regseqReadback₁ realSeal₁ transports₁
        continuations₁ provenance₁ nameCert₁ =>
        cases y with
        | mk trace₂ socket₂ streamSchedule₂ regseqReadback₂ realSeal₂ transports₂
            continuations₂ provenance₂ nameCert₂ =>
            injection h with hTrace t1
            injection t1 with hSocket t2
            injection t2 with hStreamSchedule t3
            injection t3 with hRegseqReadback t4
            injection t4 with hRealSeal t5
            injection t5 with hTransports t6
            injection t6 with hContinuations t7
            injection t7 with hProvenance t8
            injection t8 with hNameCert _
            subst hTrace
            subst hSocket
            subst hStreamSchedule
            subst hRegseqReadback
            subst hRealSeal
            subst hTransports
            subst hContinuations
            subst hProvenance
            subst hNameCert
            rfl

instance finiteTraceGapSocketNontrivial : Nontrivial FiniteTraceGapSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteTraceGapSocketUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteTraceGapSocketUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteTraceGapSocketUp :=
  finiteTraceGapSocketChapterTasteGate

theorem FiniteTraceGapSocketTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteTraceGapSocketDecodeBHist (finiteTraceGapSocketEncodeBHist h) = h) ∧
      (∀ x : FiniteTraceGapSocketUp,
        finiteTraceGapSocketFromEventFlow (finiteTraceGapSocketToEventFlow x) = some x) ∧
        (∀ x y : FiniteTraceGapSocketUp,
          finiteTraceGapSocketToEventFlow x = finiteTraceGapSocketToEventFlow y → x = y) ∧
          finiteTraceGapSocketEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact finiteTraceGapSocket_decode_encode_bhist
  · constructor
    · exact finiteTraceGapSocket_round_trip
    · constructor
      · intro x y heq
        exact finiteTraceGapSocketToEventFlow_injective heq
      · rfl

end BEDC.Derived.FiniteTraceGapSocketUp
