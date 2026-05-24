import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SignedDigitRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SignedDigitRealUp : Type where
  | mk :
      (stream window enclosure located sealRow transport route provenance cert : BHist) →
      SignedDigitRealUp
  deriving DecidableEq

def signedDigitRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: signedDigitRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: signedDigitRealEncodeBHist h

def signedDigitRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (signedDigitRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (signedDigitRealDecodeBHist tail)

private theorem signedDigitRealDecode_encode_bhist :
    ∀ h : BHist, signedDigitRealDecodeBHist (signedDigitRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def signedDigitRealToEventFlow : SignedDigitRealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SignedDigitRealUp.mk stream window enclosure located sealRow transport route provenance cert =>
      [[BMark.b0],
        signedDigitRealEncodeBHist stream,
        [BMark.b1, BMark.b0],
        signedDigitRealEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b0],
        signedDigitRealEncodeBHist enclosure,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        signedDigitRealEncodeBHist located,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        signedDigitRealEncodeBHist sealRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        signedDigitRealEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        signedDigitRealEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        signedDigitRealEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        signedDigitRealEncodeBHist cert]

def signedDigitRealFromEventFlow (ef : EventFlow) : Option SignedDigitRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | stream :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | window :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | enclosure :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | located :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | sealRow :: rest9 =>
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
                                                      | route :: rest13 =>
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
                                                                      | cert :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (SignedDigitRealUp.mk
                                                                                  (signedDigitRealDecodeBHist
                                                                                    stream)
                                                                                  (signedDigitRealDecodeBHist
                                                                                    window)
                                                                                  (signedDigitRealDecodeBHist
                                                                                    enclosure)
                                                                                  (signedDigitRealDecodeBHist
                                                                                    located)
                                                                                  (signedDigitRealDecodeBHist
                                                                                    sealRow)
                                                                                  (signedDigitRealDecodeBHist
                                                                                    transport)
                                                                                  (signedDigitRealDecodeBHist
                                                                                    route)
                                                                                  (signedDigitRealDecodeBHist
                                                                                    provenance)
                                                                                  (signedDigitRealDecodeBHist
                                                                                    cert))
                                                                          | _ :: _ =>
                                                                              none

private theorem SignedDigitRealTasteGate_single_carrier_alignment_mk_congr
    {stream stream' window window' enclosure enclosure' located located' sealRow sealRow'
      transport transport' route route' provenance provenance' cert cert' : BHist} :
    stream = stream' →
      window = window' →
        enclosure = enclosure' →
          located = located' →
            sealRow = sealRow' →
              transport = transport' →
                route = route' →
                  provenance = provenance' →
                    cert = cert' →
                      SignedDigitRealUp.mk stream window enclosure located sealRow transport route
                          provenance cert =
                        SignedDigitRealUp.mk stream' window' enclosure' located' sealRow'
                          transport' route' provenance' cert' := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hStream hWindow hEnclosure hLocated hSealRow hTransport hRoute hProvenance hCert
  cases hStream
  cases hWindow
  cases hEnclosure
  cases hLocated
  cases hSealRow
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hCert
  rfl

private theorem signedDigitReal_round_trip :
    ∀ x : SignedDigitRealUp,
      signedDigitRealFromEventFlow (signedDigitRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk stream window enclosure located sealRow transport route provenance cert =>
      change
        some
          (SignedDigitRealUp.mk
            (signedDigitRealDecodeBHist (signedDigitRealEncodeBHist stream))
            (signedDigitRealDecodeBHist (signedDigitRealEncodeBHist window))
            (signedDigitRealDecodeBHist (signedDigitRealEncodeBHist enclosure))
            (signedDigitRealDecodeBHist (signedDigitRealEncodeBHist located))
            (signedDigitRealDecodeBHist (signedDigitRealEncodeBHist sealRow))
            (signedDigitRealDecodeBHist (signedDigitRealEncodeBHist transport))
            (signedDigitRealDecodeBHist (signedDigitRealEncodeBHist route))
            (signedDigitRealDecodeBHist (signedDigitRealEncodeBHist provenance))
            (signedDigitRealDecodeBHist (signedDigitRealEncodeBHist cert))) =
          some
            (SignedDigitRealUp.mk stream window enclosure located sealRow transport route
              provenance cert)
      have hStream := signedDigitRealDecode_encode_bhist stream
      have hWindow := signedDigitRealDecode_encode_bhist window
      have hEnclosure := signedDigitRealDecode_encode_bhist enclosure
      have hLocated := signedDigitRealDecode_encode_bhist located
      have hSealRow := signedDigitRealDecode_encode_bhist sealRow
      have hTransport := signedDigitRealDecode_encode_bhist transport
      have hRoute := signedDigitRealDecode_encode_bhist route
      have hProvenance := signedDigitRealDecode_encode_bhist provenance
      have hCert := signedDigitRealDecode_encode_bhist cert
      exact congrArg some
        (SignedDigitRealTasteGate_single_carrier_alignment_mk_congr hStream hWindow hEnclosure
          hLocated hSealRow hTransport hRoute hProvenance hCert)

private theorem signedDigitRealToEventFlow_injective {x y : SignedDigitRealUp} :
    signedDigitRealToEventFlow x = signedDigitRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      signedDigitRealFromEventFlow (signedDigitRealToEventFlow x) =
        signedDigitRealFromEventFlow (signedDigitRealToEventFlow y) :=
    congrArg signedDigitRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (signedDigitReal_round_trip x).symm
      (Eq.trans hread (signedDigitReal_round_trip y)))

instance signedDigitRealBHistCarrier : BHistCarrier SignedDigitRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := signedDigitRealToEventFlow
  fromEventFlow := signedDigitRealFromEventFlow

instance signedDigitRealChapterTasteGate : ChapterTasteGate SignedDigitRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change signedDigitRealFromEventFlow (signedDigitRealToEventFlow x) = some x
    exact signedDigitReal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (signedDigitRealToEventFlow_injective heq)

def taste_gate : ChapterTasteGate SignedDigitRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  signedDigitRealChapterTasteGate

theorem SignedDigitRealTasteGate_single_carrier_alignment :
    (∀ h : BHist, signedDigitRealDecodeBHist (signedDigitRealEncodeBHist h) = h) ∧
      (∀ x : SignedDigitRealUp,
        signedDigitRealFromEventFlow (signedDigitRealToEventFlow x) = some x) ∧
        (∀ x y : SignedDigitRealUp,
          signedDigitRealToEventFlow x = signedDigitRealToEventFlow y → x = y) ∧
          signedDigitRealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact signedDigitRealDecode_encode_bhist
  · constructor
    · exact signedDigitReal_round_trip
    · constructor
      · intro x y heq
        exact signedDigitRealToEventFlow_injective heq
      · rfl

end BEDC.Derived.SignedDigitRealUp
