import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCompactIntervalOscillationBoundUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCompactIntervalOscillationBoundUp : Type where
  | mk :
      (interval compactness continuousMap finiteNet modulus dyadicLedger streamWindow
        rationalReadback realSeal transport replay provenance localNameCert : BHist) →
      LocatedCompactIntervalOscillationBoundUp
  deriving DecidableEq

def locatedCompactIntervalOscillationBoundEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCompactIntervalOscillationBoundEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCompactIntervalOscillationBoundEncodeBHist h

def locatedCompactIntervalOscillationBoundDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCompactIntervalOscillationBoundDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCompactIntervalOscillationBoundDecodeBHist tail)

private theorem locatedCompactIntervalOscillationBound_decode_encode_bhist :
    ∀ h : BHist,
      locatedCompactIntervalOscillationBoundDecodeBHist
        (locatedCompactIntervalOscillationBoundEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def locatedCompactIntervalOscillationBoundFields :
    LocatedCompactIntervalOscillationBoundUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCompactIntervalOscillationBoundUp.mk interval compactness continuousMap finiteNet
      modulus dyadicLedger streamWindow rationalReadback realSeal transport replay provenance
      localNameCert =>
      [interval, compactness, continuousMap, finiteNet, modulus, dyadicLedger, streamWindow,
        rationalReadback, realSeal, transport, replay, provenance, localNameCert]

def locatedCompactIntervalOscillationBoundToEventFlow :
    LocatedCompactIntervalOscillationBoundUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map locatedCompactIntervalOscillationBoundEncodeBHist
        (locatedCompactIntervalOscillationBoundFields x)

def locatedCompactIntervalOscillationBoundFromEventFlow :
    EventFlow → Option LocatedCompactIntervalOscillationBoundUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | interval :: rest0 =>
      match rest0 with
      | [] => none
      | compactness :: rest1 =>
          match rest1 with
          | [] => none
          | continuousMap :: rest2 =>
              match rest2 with
              | [] => none
              | finiteNet :: rest3 =>
                  match rest3 with
                  | [] => none
                  | modulus :: rest4 =>
                      match rest4 with
                      | [] => none
                      | dyadicLedger :: rest5 =>
                          match rest5 with
                          | [] => none
                          | streamWindow :: rest6 =>
                              match rest6 with
                              | [] => none
                              | rationalReadback :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | realSeal :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | replay :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | provenance :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | localNameCert :: rest12 =>
                                                      match rest12 with
                                                      | [] =>
                                                          some
                                                            (LocatedCompactIntervalOscillationBoundUp.mk
                                                              (locatedCompactIntervalOscillationBoundDecodeBHist
                                                                interval)
                                                              (locatedCompactIntervalOscillationBoundDecodeBHist
                                                                compactness)
                                                              (locatedCompactIntervalOscillationBoundDecodeBHist
                                                                continuousMap)
                                                              (locatedCompactIntervalOscillationBoundDecodeBHist
                                                                finiteNet)
                                                              (locatedCompactIntervalOscillationBoundDecodeBHist
                                                                modulus)
                                                              (locatedCompactIntervalOscillationBoundDecodeBHist
                                                                dyadicLedger)
                                                              (locatedCompactIntervalOscillationBoundDecodeBHist
                                                                streamWindow)
                                                              (locatedCompactIntervalOscillationBoundDecodeBHist
                                                                rationalReadback)
                                                              (locatedCompactIntervalOscillationBoundDecodeBHist
                                                                realSeal)
                                                              (locatedCompactIntervalOscillationBoundDecodeBHist
                                                                transport)
                                                              (locatedCompactIntervalOscillationBoundDecodeBHist
                                                                replay)
                                                              (locatedCompactIntervalOscillationBoundDecodeBHist
                                                                provenance)
                                                              (locatedCompactIntervalOscillationBoundDecodeBHist
                                                                localNameCert))
                                                      | _ :: _ => none

private theorem locatedCompactIntervalOscillationBound_round_trip :
    ∀ x : LocatedCompactIntervalOscillationBoundUp,
      locatedCompactIntervalOscillationBoundFromEventFlow
        (locatedCompactIntervalOscillationBoundToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk interval compactness continuousMap finiteNet modulus dyadicLedger streamWindow
      rationalReadback realSeal transport replay provenance localNameCert =>
      change
        some
          (LocatedCompactIntervalOscillationBoundUp.mk
            (locatedCompactIntervalOscillationBoundDecodeBHist
              (locatedCompactIntervalOscillationBoundEncodeBHist interval))
            (locatedCompactIntervalOscillationBoundDecodeBHist
              (locatedCompactIntervalOscillationBoundEncodeBHist compactness))
            (locatedCompactIntervalOscillationBoundDecodeBHist
              (locatedCompactIntervalOscillationBoundEncodeBHist continuousMap))
            (locatedCompactIntervalOscillationBoundDecodeBHist
              (locatedCompactIntervalOscillationBoundEncodeBHist finiteNet))
            (locatedCompactIntervalOscillationBoundDecodeBHist
              (locatedCompactIntervalOscillationBoundEncodeBHist modulus))
            (locatedCompactIntervalOscillationBoundDecodeBHist
              (locatedCompactIntervalOscillationBoundEncodeBHist dyadicLedger))
            (locatedCompactIntervalOscillationBoundDecodeBHist
              (locatedCompactIntervalOscillationBoundEncodeBHist streamWindow))
            (locatedCompactIntervalOscillationBoundDecodeBHist
              (locatedCompactIntervalOscillationBoundEncodeBHist rationalReadback))
            (locatedCompactIntervalOscillationBoundDecodeBHist
              (locatedCompactIntervalOscillationBoundEncodeBHist realSeal))
            (locatedCompactIntervalOscillationBoundDecodeBHist
              (locatedCompactIntervalOscillationBoundEncodeBHist transport))
            (locatedCompactIntervalOscillationBoundDecodeBHist
              (locatedCompactIntervalOscillationBoundEncodeBHist replay))
            (locatedCompactIntervalOscillationBoundDecodeBHist
              (locatedCompactIntervalOscillationBoundEncodeBHist provenance))
            (locatedCompactIntervalOscillationBoundDecodeBHist
              (locatedCompactIntervalOscillationBoundEncodeBHist localNameCert))) =
          some
            (LocatedCompactIntervalOscillationBoundUp.mk interval compactness continuousMap
              finiteNet modulus dyadicLedger streamWindow rationalReadback realSeal transport
              replay provenance localNameCert)
      rw [locatedCompactIntervalOscillationBound_decode_encode_bhist interval,
        locatedCompactIntervalOscillationBound_decode_encode_bhist compactness,
        locatedCompactIntervalOscillationBound_decode_encode_bhist continuousMap,
        locatedCompactIntervalOscillationBound_decode_encode_bhist finiteNet,
        locatedCompactIntervalOscillationBound_decode_encode_bhist modulus,
        locatedCompactIntervalOscillationBound_decode_encode_bhist dyadicLedger,
        locatedCompactIntervalOscillationBound_decode_encode_bhist streamWindow,
        locatedCompactIntervalOscillationBound_decode_encode_bhist rationalReadback,
        locatedCompactIntervalOscillationBound_decode_encode_bhist realSeal,
        locatedCompactIntervalOscillationBound_decode_encode_bhist transport,
        locatedCompactIntervalOscillationBound_decode_encode_bhist replay,
        locatedCompactIntervalOscillationBound_decode_encode_bhist provenance,
        locatedCompactIntervalOscillationBound_decode_encode_bhist localNameCert]

private theorem locatedCompactIntervalOscillationBoundToEventFlow_injective
    {x y : LocatedCompactIntervalOscillationBoundUp} :
    locatedCompactIntervalOscillationBoundToEventFlow x =
      locatedCompactIntervalOscillationBoundToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCompactIntervalOscillationBoundFromEventFlow
          (locatedCompactIntervalOscillationBoundToEventFlow x) =
        locatedCompactIntervalOscillationBoundFromEventFlow
          (locatedCompactIntervalOscillationBoundToEventFlow y) :=
    congrArg locatedCompactIntervalOscillationBoundFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedCompactIntervalOscillationBound_round_trip x).symm
      (Eq.trans hread (locatedCompactIntervalOscillationBound_round_trip y)))

instance locatedCompactIntervalOscillationBoundBHistCarrier :
    BHistCarrier LocatedCompactIntervalOscillationBoundUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCompactIntervalOscillationBoundToEventFlow
  fromEventFlow := locatedCompactIntervalOscillationBoundFromEventFlow

instance locatedCompactIntervalOscillationBoundChapterTasteGate :
    ChapterTasteGate LocatedCompactIntervalOscillationBoundUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedCompactIntervalOscillationBoundFromEventFlow
      (locatedCompactIntervalOscillationBoundToEventFlow x) = some x
    exact locatedCompactIntervalOscillationBound_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedCompactIntervalOscillationBoundToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedCompactIntervalOscillationBoundUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedCompactIntervalOscillationBoundChapterTasteGate

theorem LocatedCompactIntervalOscillationBoundTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedCompactIntervalOscillationBoundDecodeBHist
        (locatedCompactIntervalOscillationBoundEncodeBHist h) = h) ∧
      (∀ x : LocatedCompactIntervalOscillationBoundUp,
        locatedCompactIntervalOscillationBoundFromEventFlow
          (locatedCompactIntervalOscillationBoundToEventFlow x) = some x) ∧
        (∀ x y : LocatedCompactIntervalOscillationBoundUp,
          locatedCompactIntervalOscillationBoundToEventFlow x =
            locatedCompactIntervalOscillationBoundToEventFlow y → x = y) ∧
          locatedCompactIntervalOscillationBoundEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact locatedCompactIntervalOscillationBound_decode_encode_bhist
  · constructor
    · exact locatedCompactIntervalOscillationBound_round_trip
    · constructor
      · intro x y heq
        exact locatedCompactIntervalOscillationBoundToEventFlow_injective heq
      · rfl

end BEDC.Derived.LocatedCompactIntervalOscillationBoundUp
