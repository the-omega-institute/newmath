import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCompactUp : Type where
  | mk :
      (carrier locatedness finiteNet apartness transport continuation provenance
        nameCert : BHist) →
      LocatedCompactUp
  deriving DecidableEq

def locatedCompactEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCompactEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCompactEncodeBHist h

def locatedCompactDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCompactDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCompactDecodeBHist tail)

private theorem LocatedCompactTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, locatedCompactDecodeBHist (locatedCompactEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedCompactToEventFlow : LocatedCompactUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCompactUp.mk carrier locatedness finiteNet apartness transport continuation
      provenance nameCert =>
      [[BMark.b0],
        locatedCompactEncodeBHist carrier,
        [BMark.b1, BMark.b0],
        locatedCompactEncodeBHist locatedness,
        [BMark.b1, BMark.b1, BMark.b0],
        locatedCompactEncodeBHist finiteNet,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedCompactEncodeBHist apartness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedCompactEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedCompactEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedCompactEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        locatedCompactEncodeBHist nameCert]

def locatedCompactFromEventFlow : EventFlow → Option LocatedCompactUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | carrier :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | locatedness :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | finiteNet :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | apartness :: rest7 =>
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
                                              | continuation :: rest11 =>
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
                                                              | nameCert :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (LocatedCompactUp.mk
                                                                          (locatedCompactDecodeBHist carrier)
                                                                          (locatedCompactDecodeBHist locatedness)
                                                                          (locatedCompactDecodeBHist finiteNet)
                                                                          (locatedCompactDecodeBHist apartness)
                                                                          (locatedCompactDecodeBHist transport)
                                                                          (locatedCompactDecodeBHist continuation)
                                                                          (locatedCompactDecodeBHist provenance)
                                                                          (locatedCompactDecodeBHist nameCert))
                                                                  | _ :: _ => none

private theorem locatedCompact_round_trip :
    ∀ x : LocatedCompactUp,
      locatedCompactFromEventFlow (locatedCompactToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk carrier locatedness finiteNet apartness transport continuation provenance nameCert =>
      change
        some
          (LocatedCompactUp.mk
            (locatedCompactDecodeBHist (locatedCompactEncodeBHist carrier))
            (locatedCompactDecodeBHist (locatedCompactEncodeBHist locatedness))
            (locatedCompactDecodeBHist (locatedCompactEncodeBHist finiteNet))
            (locatedCompactDecodeBHist (locatedCompactEncodeBHist apartness))
            (locatedCompactDecodeBHist (locatedCompactEncodeBHist transport))
            (locatedCompactDecodeBHist (locatedCompactEncodeBHist continuation))
            (locatedCompactDecodeBHist (locatedCompactEncodeBHist provenance))
            (locatedCompactDecodeBHist (locatedCompactEncodeBHist nameCert))) =
          some
            (LocatedCompactUp.mk carrier locatedness finiteNet apartness transport
              continuation provenance nameCert)
      have hCarrier :=
        LocatedCompactTasteGate_single_carrier_alignment_decode_encode carrier
      have hLocatedness :=
        LocatedCompactTasteGate_single_carrier_alignment_decode_encode locatedness
      have hFiniteNet :=
        LocatedCompactTasteGate_single_carrier_alignment_decode_encode finiteNet
      have hApartness :=
        LocatedCompactTasteGate_single_carrier_alignment_decode_encode apartness
      have hTransport :=
        LocatedCompactTasteGate_single_carrier_alignment_decode_encode transport
      have hContinuation :=
        LocatedCompactTasteGate_single_carrier_alignment_decode_encode continuation
      have hProvenance :=
        LocatedCompactTasteGate_single_carrier_alignment_decode_encode provenance
      have hNameCert :=
        LocatedCompactTasteGate_single_carrier_alignment_decode_encode nameCert
      rw [hCarrier, hLocatedness, hFiniteNet, hApartness, hTransport, hContinuation,
        hProvenance, hNameCert]

private theorem locatedCompactToEventFlow_injective {x y : LocatedCompactUp} :
    locatedCompactToEventFlow x = locatedCompactToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCompactFromEventFlow (locatedCompactToEventFlow x) =
        locatedCompactFromEventFlow (locatedCompactToEventFlow y) :=
    congrArg locatedCompactFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedCompact_round_trip x).symm
      (Eq.trans hread (locatedCompact_round_trip y)))

instance locatedCompactBHistCarrier : BHistCarrier LocatedCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCompactToEventFlow
  fromEventFlow := locatedCompactFromEventFlow

instance locatedCompactChapterTasteGate : ChapterTasteGate LocatedCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedCompactFromEventFlow (locatedCompactToEventFlow x) = some x
    exact locatedCompact_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedCompactToEventFlow_injective heq)

theorem LocatedCompactTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedCompactDecodeBHist (locatedCompactEncodeBHist h) = h) ∧
      (∀ x : LocatedCompactUp,
        locatedCompactFromEventFlow (locatedCompactToEventFlow x) = some x) ∧
        (∀ x y : LocatedCompactUp,
          locatedCompactToEventFlow x = locatedCompactToEventFlow y → x = y) ∧
          locatedCompactEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact LocatedCompactTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact locatedCompact_round_trip
    · constructor
      · intro x y heq
        exact locatedCompactToEventFlow_injective heq
      · rfl

end BEDC.Derived.LocatedCompactUp
