import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyLocatedModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyLocatedModulusUp : Type where
  | mk :
      (dyadicLedger streamWindow regularReadback lowerComparison upperComparison modulusRow
        transportRow replayRow provenanceRow nameRow : BHist) →
      RegularCauchyLocatedModulusUp
  deriving DecidableEq

def regularCauchyLocatedModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyLocatedModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyLocatedModulusEncodeBHist h

def regularCauchyLocatedModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyLocatedModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyLocatedModulusDecodeBHist tail)

private theorem regularCauchyLocatedModulus_decode_encode_bhist :
    ∀ h : BHist,
      regularCauchyLocatedModulusDecodeBHist
        (regularCauchyLocatedModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem regularCauchyLocatedModulus_mk_congr
    {dyadicLedger dyadicLedger' streamWindow streamWindow' regularReadback regularReadback'
      lowerComparison lowerComparison' upperComparison upperComparison' modulusRow modulusRow'
      transportRow transportRow' replayRow replayRow' provenanceRow provenanceRow'
      nameRow nameRow' : BHist}
    (hDyadic : dyadicLedger' = dyadicLedger)
    (hStream : streamWindow' = streamWindow)
    (hReadback : regularReadback' = regularReadback)
    (hLower : lowerComparison' = lowerComparison)
    (hUpper : upperComparison' = upperComparison)
    (hModulus : modulusRow' = modulusRow)
    (hTransport : transportRow' = transportRow)
    (hReplay : replayRow' = replayRow)
    (hProvenance : provenanceRow' = provenanceRow)
    (hName : nameRow' = nameRow) :
    RegularCauchyLocatedModulusUp.mk dyadicLedger' streamWindow' regularReadback'
        lowerComparison' upperComparison' modulusRow' transportRow' replayRow' provenanceRow'
        nameRow' =
      RegularCauchyLocatedModulusUp.mk dyadicLedger streamWindow regularReadback
        lowerComparison upperComparison modulusRow transportRow replayRow provenanceRow nameRow := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hDyadic
  cases hStream
  cases hReadback
  cases hLower
  cases hUpper
  cases hModulus
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hName
  rfl

def regularCauchyLocatedModulusToEventFlow :
    RegularCauchyLocatedModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyLocatedModulusUp.mk dyadicLedger streamWindow regularReadback
      lowerComparison upperComparison modulusRow transportRow replayRow provenanceRow nameRow =>
      [[BMark.b0],
        regularCauchyLocatedModulusEncodeBHist dyadicLedger,
        [BMark.b1, BMark.b0],
        regularCauchyLocatedModulusEncodeBHist streamWindow,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyLocatedModulusEncodeBHist regularReadback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyLocatedModulusEncodeBHist lowerComparison,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyLocatedModulusEncodeBHist upperComparison,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyLocatedModulusEncodeBHist modulusRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyLocatedModulusEncodeBHist transportRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyLocatedModulusEncodeBHist replayRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyLocatedModulusEncodeBHist provenanceRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchyLocatedModulusEncodeBHist nameRow]

def regularCauchyLocatedModulusFromEventFlow :
    EventFlow → Option RegularCauchyLocatedModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | dyadicLedger :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | streamWindow :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | regularReadback :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | lowerComparison :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | upperComparison :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | modulusRow :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transportRow :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | replayRow :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenanceRow :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | nameRow :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (RegularCauchyLocatedModulusUp.mk
                                                                                          (regularCauchyLocatedModulusDecodeBHist
                                                                                            dyadicLedger)
                                                                                          (regularCauchyLocatedModulusDecodeBHist
                                                                                            streamWindow)
                                                                                          (regularCauchyLocatedModulusDecodeBHist
                                                                                            regularReadback)
                                                                                          (regularCauchyLocatedModulusDecodeBHist
                                                                                            lowerComparison)
                                                                                          (regularCauchyLocatedModulusDecodeBHist
                                                                                            upperComparison)
                                                                                          (regularCauchyLocatedModulusDecodeBHist
                                                                                            modulusRow)
                                                                                          (regularCauchyLocatedModulusDecodeBHist
                                                                                            transportRow)
                                                                                          (regularCauchyLocatedModulusDecodeBHist
                                                                                            replayRow)
                                                                                          (regularCauchyLocatedModulusDecodeBHist
                                                                                            provenanceRow)
                                                                                          (regularCauchyLocatedModulusDecodeBHist
                                                                                            nameRow))
                                                                                  | _ :: _ => none

private theorem regularCauchyLocatedModulus_round_trip :
    ∀ x : RegularCauchyLocatedModulusUp,
      regularCauchyLocatedModulusFromEventFlow
        (regularCauchyLocatedModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk dyadicLedger streamWindow regularReadback lowerComparison upperComparison modulusRow
      transportRow replayRow provenanceRow nameRow =>
      change
        some
          (RegularCauchyLocatedModulusUp.mk
            (regularCauchyLocatedModulusDecodeBHist
              (regularCauchyLocatedModulusEncodeBHist dyadicLedger))
            (regularCauchyLocatedModulusDecodeBHist
              (regularCauchyLocatedModulusEncodeBHist streamWindow))
            (regularCauchyLocatedModulusDecodeBHist
              (regularCauchyLocatedModulusEncodeBHist regularReadback))
            (regularCauchyLocatedModulusDecodeBHist
              (regularCauchyLocatedModulusEncodeBHist lowerComparison))
            (regularCauchyLocatedModulusDecodeBHist
              (regularCauchyLocatedModulusEncodeBHist upperComparison))
            (regularCauchyLocatedModulusDecodeBHist
              (regularCauchyLocatedModulusEncodeBHist modulusRow))
            (regularCauchyLocatedModulusDecodeBHist
              (regularCauchyLocatedModulusEncodeBHist transportRow))
            (regularCauchyLocatedModulusDecodeBHist
              (regularCauchyLocatedModulusEncodeBHist replayRow))
            (regularCauchyLocatedModulusDecodeBHist
              (regularCauchyLocatedModulusEncodeBHist provenanceRow))
            (regularCauchyLocatedModulusDecodeBHist
              (regularCauchyLocatedModulusEncodeBHist nameRow))) =
          some
            (RegularCauchyLocatedModulusUp.mk dyadicLedger streamWindow regularReadback
              lowerComparison upperComparison modulusRow transportRow replayRow provenanceRow nameRow)
      exact
        congrArg some
          (regularCauchyLocatedModulus_mk_congr
            (regularCauchyLocatedModulus_decode_encode_bhist dyadicLedger)
            (regularCauchyLocatedModulus_decode_encode_bhist streamWindow)
            (regularCauchyLocatedModulus_decode_encode_bhist regularReadback)
            (regularCauchyLocatedModulus_decode_encode_bhist lowerComparison)
            (regularCauchyLocatedModulus_decode_encode_bhist upperComparison)
            (regularCauchyLocatedModulus_decode_encode_bhist modulusRow)
            (regularCauchyLocatedModulus_decode_encode_bhist transportRow)
            (regularCauchyLocatedModulus_decode_encode_bhist replayRow)
            (regularCauchyLocatedModulus_decode_encode_bhist provenanceRow)
            (regularCauchyLocatedModulus_decode_encode_bhist nameRow))

private theorem regularCauchyLocatedModulusToEventFlow_injective
    {x y : RegularCauchyLocatedModulusUp} :
    regularCauchyLocatedModulusToEventFlow x =
      regularCauchyLocatedModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyLocatedModulusFromEventFlow
          (regularCauchyLocatedModulusToEventFlow x) =
        regularCauchyLocatedModulusFromEventFlow
          (regularCauchyLocatedModulusToEventFlow y) :=
    congrArg regularCauchyLocatedModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyLocatedModulus_round_trip x).symm
      (Eq.trans hread (regularCauchyLocatedModulus_round_trip y)))

instance regularCauchyLocatedModulusBHistCarrier :
    BHistCarrier RegularCauchyLocatedModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyLocatedModulusToEventFlow
  fromEventFlow := regularCauchyLocatedModulusFromEventFlow

instance regularCauchyLocatedModulusChapterTasteGate :
    ChapterTasteGate RegularCauchyLocatedModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    change
      ∀ x : RegularCauchyLocatedModulusUp,
        regularCauchyLocatedModulusFromEventFlow
          (regularCauchyLocatedModulusToEventFlow x) = some x
    exact regularCauchyLocatedModulus_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyLocatedModulusToEventFlow_injective heq)

theorem RegularCauchyLocatedModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyLocatedModulusDecodeBHist
        (regularCauchyLocatedModulusEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyLocatedModulusUp,
        regularCauchyLocatedModulusFromEventFlow
          (regularCauchyLocatedModulusToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyLocatedModulusUp,
          regularCauchyLocatedModulusToEventFlow x =
            regularCauchyLocatedModulusToEventFlow y → x = y) ∧
          regularCauchyLocatedModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyLocatedModulus_decode_encode_bhist
  · constructor
    · exact regularCauchyLocatedModulus_round_trip
    · constructor
      · intro x y heq
        exact regularCauchyLocatedModulusToEventFlow_injective heq
      · rfl

end BEDC.Derived.RegularCauchyLocatedModulusUp
