import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyCompletionUnitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyCompletionUnitUp : Type where
  | mk :
      (source unitAdmission streamWindows dyadicLedger sealHandoff transportRow replayRow
        provenanceRow nameRow : BHist) →
      RegularCauchyCompletionUnitUp
  deriving DecidableEq

def regularCauchyCompletionUnitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyCompletionUnitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyCompletionUnitEncodeBHist h

def regularCauchyCompletionUnitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyCompletionUnitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyCompletionUnitDecodeBHist tail)

private theorem regularCauchyCompletionUnit_decode_encode_bhist :
    ∀ h : BHist,
      regularCauchyCompletionUnitDecodeBHist
        (regularCauchyCompletionUnitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem regularCauchyCompletionUnit_mk_congr
    {source source' unitAdmission unitAdmission' streamWindows streamWindows'
      dyadicLedger dyadicLedger' sealHandoff sealHandoff' transportRow transportRow'
      replayRow replayRow' provenanceRow provenanceRow' nameRow nameRow' : BHist}
    (hSource : source' = source)
    (hUnit : unitAdmission' = unitAdmission)
    (hStream : streamWindows' = streamWindows)
    (hDyadic : dyadicLedger' = dyadicLedger)
    (hSeal : sealHandoff' = sealHandoff)
    (hTransport : transportRow' = transportRow)
    (hReplay : replayRow' = replayRow)
    (hProvenance : provenanceRow' = provenanceRow)
    (hName : nameRow' = nameRow) :
    RegularCauchyCompletionUnitUp.mk source' unitAdmission' streamWindows' dyadicLedger'
        sealHandoff' transportRow' replayRow' provenanceRow' nameRow' =
      RegularCauchyCompletionUnitUp.mk source unitAdmission streamWindows dyadicLedger
        sealHandoff transportRow replayRow provenanceRow nameRow := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSource
  cases hUnit
  cases hStream
  cases hDyadic
  cases hSeal
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hName
  rfl

def regularCauchyCompletionUnitToEventFlow :
    RegularCauchyCompletionUnitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyCompletionUnitUp.mk source unitAdmission streamWindows dyadicLedger
      sealHandoff transportRow replayRow provenanceRow nameRow =>
      [[BMark.b0],
        regularCauchyCompletionUnitEncodeBHist source,
        [BMark.b1, BMark.b0],
        regularCauchyCompletionUnitEncodeBHist unitAdmission,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCompletionUnitEncodeBHist streamWindows,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCompletionUnitEncodeBHist dyadicLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCompletionUnitEncodeBHist sealHandoff,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCompletionUnitEncodeBHist transportRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCompletionUnitEncodeBHist replayRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyCompletionUnitEncodeBHist provenanceRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyCompletionUnitEncodeBHist nameRow]

def regularCauchyCompletionUnitFromEventFlow :
    EventFlow → Option RegularCauchyCompletionUnitUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | source :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | unitAdmission :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | streamWindows :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | dyadicLedger :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | sealHandoff :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transportRow :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | replayRow :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenanceRow :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | nameRow :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (RegularCauchyCompletionUnitUp.mk
                                                                                  (regularCauchyCompletionUnitDecodeBHist
                                                                                    source)
                                                                                  (regularCauchyCompletionUnitDecodeBHist
                                                                                    unitAdmission)
                                                                                  (regularCauchyCompletionUnitDecodeBHist
                                                                                    streamWindows)
                                                                                  (regularCauchyCompletionUnitDecodeBHist
                                                                                    dyadicLedger)
                                                                                  (regularCauchyCompletionUnitDecodeBHist
                                                                                    sealHandoff)
                                                                                  (regularCauchyCompletionUnitDecodeBHist
                                                                                    transportRow)
                                                                                  (regularCauchyCompletionUnitDecodeBHist
                                                                                    replayRow)
                                                                                  (regularCauchyCompletionUnitDecodeBHist
                                                                                    provenanceRow)
                                                                                  (regularCauchyCompletionUnitDecodeBHist
                                                                                    nameRow))
                                                                          | _ :: _ => none

private theorem regularCauchyCompletionUnit_round_trip :
    ∀ x : RegularCauchyCompletionUnitUp,
      regularCauchyCompletionUnitFromEventFlow
        (regularCauchyCompletionUnitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source unitAdmission streamWindows dyadicLedger sealHandoff transportRow replayRow
      provenanceRow nameRow =>
      change
        some
          (RegularCauchyCompletionUnitUp.mk
            (regularCauchyCompletionUnitDecodeBHist
              (regularCauchyCompletionUnitEncodeBHist source))
            (regularCauchyCompletionUnitDecodeBHist
              (regularCauchyCompletionUnitEncodeBHist unitAdmission))
            (regularCauchyCompletionUnitDecodeBHist
              (regularCauchyCompletionUnitEncodeBHist streamWindows))
            (regularCauchyCompletionUnitDecodeBHist
              (regularCauchyCompletionUnitEncodeBHist dyadicLedger))
            (regularCauchyCompletionUnitDecodeBHist
              (regularCauchyCompletionUnitEncodeBHist sealHandoff))
            (regularCauchyCompletionUnitDecodeBHist
              (regularCauchyCompletionUnitEncodeBHist transportRow))
            (regularCauchyCompletionUnitDecodeBHist
              (regularCauchyCompletionUnitEncodeBHist replayRow))
            (regularCauchyCompletionUnitDecodeBHist
              (regularCauchyCompletionUnitEncodeBHist provenanceRow))
            (regularCauchyCompletionUnitDecodeBHist
              (regularCauchyCompletionUnitEncodeBHist nameRow))) =
          some
            (RegularCauchyCompletionUnitUp.mk source unitAdmission streamWindows dyadicLedger
              sealHandoff transportRow replayRow provenanceRow nameRow)
      exact
        congrArg some
          (regularCauchyCompletionUnit_mk_congr
            (regularCauchyCompletionUnit_decode_encode_bhist source)
            (regularCauchyCompletionUnit_decode_encode_bhist unitAdmission)
            (regularCauchyCompletionUnit_decode_encode_bhist streamWindows)
            (regularCauchyCompletionUnit_decode_encode_bhist dyadicLedger)
            (regularCauchyCompletionUnit_decode_encode_bhist sealHandoff)
            (regularCauchyCompletionUnit_decode_encode_bhist transportRow)
            (regularCauchyCompletionUnit_decode_encode_bhist replayRow)
            (regularCauchyCompletionUnit_decode_encode_bhist provenanceRow)
            (regularCauchyCompletionUnit_decode_encode_bhist nameRow))

private theorem regularCauchyCompletionUnitToEventFlow_injective
    {x y : RegularCauchyCompletionUnitUp} :
    regularCauchyCompletionUnitToEventFlow x =
      regularCauchyCompletionUnitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyCompletionUnitFromEventFlow
          (regularCauchyCompletionUnitToEventFlow x) =
        regularCauchyCompletionUnitFromEventFlow
          (regularCauchyCompletionUnitToEventFlow y) :=
    congrArg regularCauchyCompletionUnitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyCompletionUnit_round_trip x).symm
      (Eq.trans hread (regularCauchyCompletionUnit_round_trip y)))

instance regularCauchyCompletionUnitBHistCarrier :
    BHistCarrier RegularCauchyCompletionUnitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyCompletionUnitToEventFlow
  fromEventFlow := regularCauchyCompletionUnitFromEventFlow

instance regularCauchyCompletionUnitChapterTasteGate :
    ChapterTasteGate RegularCauchyCompletionUnitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    change
      ∀ x : RegularCauchyCompletionUnitUp,
        regularCauchyCompletionUnitFromEventFlow
          (regularCauchyCompletionUnitToEventFlow x) = some x
    exact regularCauchyCompletionUnit_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyCompletionUnitToEventFlow_injective heq)

theorem RegularCauchyCompletionUnitTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyCompletionUnitDecodeBHist
        (regularCauchyCompletionUnitEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyCompletionUnitUp,
        regularCauchyCompletionUnitFromEventFlow
          (regularCauchyCompletionUnitToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyCompletionUnitUp,
          regularCauchyCompletionUnitToEventFlow x =
            regularCauchyCompletionUnitToEventFlow y → x = y) ∧
          regularCauchyCompletionUnitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyCompletionUnit_decode_encode_bhist
  · constructor
    · exact regularCauchyCompletionUnit_round_trip
    · constructor
      · intro x y heq
        exact regularCauchyCompletionUnitToEventFlow_injective heq
      · rfl

end BEDC.Derived.RegularCauchyCompletionUnitUp
