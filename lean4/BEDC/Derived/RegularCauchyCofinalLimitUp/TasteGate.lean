import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyCofinalLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyCofinalLimitUp : Type where
  | mk :
      (family schedule window tolerance readback sealRow transportRow continuationRow provenanceRow nameRow :
        BHist) →
      RegularCauchyCofinalLimitUp
  deriving DecidableEq

def regularCauchyCofinalLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyCofinalLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyCofinalLimitEncodeBHist h

def regularCauchyCofinalLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyCofinalLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyCofinalLimitDecodeBHist tail)

private theorem regularCauchyCofinalLimitDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchyCofinalLimitDecodeBHist (regularCauchyCofinalLimitEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem regularCauchyCofinalLimit_mk_congr
    {family family' schedule schedule' window window' tolerance tolerance'
      readback readback' sealRow sealRow' transportRow transportRow' continuationRow continuationRow'
      provenanceRow provenanceRow' nameRow nameRow' : BHist}
    (hFamily : family' = family)
    (hSchedule : schedule' = schedule)
    (hWindow : window' = window)
    (hTolerance : tolerance' = tolerance)
    (hReadback : readback' = readback)
    (hSeal : sealRow' = sealRow)
    (hTransport : transportRow' = transportRow)
    (hContinuation : continuationRow' = continuationRow)
    (hProvenance : provenanceRow' = provenanceRow)
    (hName : nameRow' = nameRow) :
    RegularCauchyCofinalLimitUp.mk family' schedule' window' tolerance' readback'
        sealRow' transportRow' continuationRow' provenanceRow' nameRow' =
      RegularCauchyCofinalLimitUp.mk family schedule window tolerance readback sealRow
        transportRow continuationRow provenanceRow nameRow := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hFamily
  cases hSchedule
  cases hWindow
  cases hTolerance
  cases hReadback
  cases hSeal
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hName
  rfl

def regularCauchyCofinalLimitToEventFlow :
    RegularCauchyCofinalLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyCofinalLimitUp.mk family schedule window tolerance readback sealRow
      transportRow continuationRow provenanceRow nameRow =>
      [[BMark.b0],
        regularCauchyCofinalLimitEncodeBHist family,
        [BMark.b1, BMark.b0],
        regularCauchyCofinalLimitEncodeBHist schedule,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCofinalLimitEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCofinalLimitEncodeBHist tolerance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCofinalLimitEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCofinalLimitEncodeBHist sealRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCofinalLimitEncodeBHist transportRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyCofinalLimitEncodeBHist continuationRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyCofinalLimitEncodeBHist provenanceRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCofinalLimitEncodeBHist nameRow]

def regularCauchyCofinalLimitFromEventFlow :
    EventFlow → Option RegularCauchyCofinalLimitUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | family :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | schedule :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | window :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | tolerance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | readback :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | sealRow :: rest11 =>
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
                                                              | continuationRow :: rest15 =>
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
                                                                                        (RegularCauchyCofinalLimitUp.mk
                                                                                          (regularCauchyCofinalLimitDecodeBHist
                                                                                            family)
                                                                                          (regularCauchyCofinalLimitDecodeBHist
                                                                                            schedule)
                                                                                          (regularCauchyCofinalLimitDecodeBHist
                                                                                            window)
                                                                                          (regularCauchyCofinalLimitDecodeBHist
                                                                                            tolerance)
                                                                                          (regularCauchyCofinalLimitDecodeBHist
                                                                                            readback)
                                                                                          (regularCauchyCofinalLimitDecodeBHist
                                                                                            sealRow)
                                                                                          (regularCauchyCofinalLimitDecodeBHist
                                                                                            transportRow)
                                                                                          (regularCauchyCofinalLimitDecodeBHist
                                                                                            continuationRow)
                                                                                          (regularCauchyCofinalLimitDecodeBHist
                                                                                            provenanceRow)
                                                                                          (regularCauchyCofinalLimitDecodeBHist
                                                                                            nameRow))
                                                                                  | _ :: _ => none

private theorem regularCauchyCofinalLimit_round_trip :
    ∀ x : RegularCauchyCofinalLimitUp,
      regularCauchyCofinalLimitFromEventFlow
        (regularCauchyCofinalLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk family schedule window tolerance readback sealRow transportRow continuationRow provenanceRow nameRow =>
      change
        some
          (RegularCauchyCofinalLimitUp.mk
            (regularCauchyCofinalLimitDecodeBHist
              (regularCauchyCofinalLimitEncodeBHist family))
            (regularCauchyCofinalLimitDecodeBHist
              (regularCauchyCofinalLimitEncodeBHist schedule))
            (regularCauchyCofinalLimitDecodeBHist
              (regularCauchyCofinalLimitEncodeBHist window))
            (regularCauchyCofinalLimitDecodeBHist
              (regularCauchyCofinalLimitEncodeBHist tolerance))
            (regularCauchyCofinalLimitDecodeBHist
              (regularCauchyCofinalLimitEncodeBHist readback))
            (regularCauchyCofinalLimitDecodeBHist
              (regularCauchyCofinalLimitEncodeBHist sealRow))
            (regularCauchyCofinalLimitDecodeBHist
              (regularCauchyCofinalLimitEncodeBHist transportRow))
            (regularCauchyCofinalLimitDecodeBHist
              (regularCauchyCofinalLimitEncodeBHist continuationRow))
            (regularCauchyCofinalLimitDecodeBHist
              (regularCauchyCofinalLimitEncodeBHist provenanceRow))
            (regularCauchyCofinalLimitDecodeBHist
              (regularCauchyCofinalLimitEncodeBHist nameRow))) =
          some
            (RegularCauchyCofinalLimitUp.mk family schedule window tolerance readback sealRow
              transportRow continuationRow provenanceRow nameRow)
      exact
        congrArg some
          (regularCauchyCofinalLimit_mk_congr
            (regularCauchyCofinalLimitDecode_encode_bhist family)
            (regularCauchyCofinalLimitDecode_encode_bhist schedule)
            (regularCauchyCofinalLimitDecode_encode_bhist window)
            (regularCauchyCofinalLimitDecode_encode_bhist tolerance)
            (regularCauchyCofinalLimitDecode_encode_bhist readback)
            (regularCauchyCofinalLimitDecode_encode_bhist sealRow)
            (regularCauchyCofinalLimitDecode_encode_bhist transportRow)
            (regularCauchyCofinalLimitDecode_encode_bhist continuationRow)
            (regularCauchyCofinalLimitDecode_encode_bhist provenanceRow)
            (regularCauchyCofinalLimitDecode_encode_bhist nameRow))

private theorem regularCauchyCofinalLimitToEventFlow_injective
    {x y : RegularCauchyCofinalLimitUp} :
    regularCauchyCofinalLimitToEventFlow x =
      regularCauchyCofinalLimitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyCofinalLimitFromEventFlow
          (regularCauchyCofinalLimitToEventFlow x) =
        regularCauchyCofinalLimitFromEventFlow
          (regularCauchyCofinalLimitToEventFlow y) :=
    congrArg regularCauchyCofinalLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyCofinalLimit_round_trip x).symm
      (Eq.trans hread (regularCauchyCofinalLimit_round_trip y)))

instance regularCauchyCofinalLimitBHistCarrier :
    BHistCarrier RegularCauchyCofinalLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyCofinalLimitToEventFlow
  fromEventFlow := regularCauchyCofinalLimitFromEventFlow

instance regularCauchyCofinalLimitChapterTasteGate :
    ChapterTasteGate RegularCauchyCofinalLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyCofinalLimitFromEventFlow
        (regularCauchyCofinalLimitToEventFlow x) = some x
    exact regularCauchyCofinalLimit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyCofinalLimitToEventFlow_injective heq)

theorem RegularCauchyCofinalLimitTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyCofinalLimitDecodeBHist
        (regularCauchyCofinalLimitEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyCofinalLimitUp,
        regularCauchyCofinalLimitFromEventFlow
          (regularCauchyCofinalLimitToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyCofinalLimitUp,
          regularCauchyCofinalLimitToEventFlow x =
            regularCauchyCofinalLimitToEventFlow y → x = y) ∧
          regularCauchyCofinalLimitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyCofinalLimitDecode_encode_bhist
  · constructor
    · exact regularCauchyCofinalLimit_round_trip
    · constructor
      · intro x y heq
        exact regularCauchyCofinalLimitToEventFlow_injective heq
      · rfl

end BEDC.Derived.RegularCauchyCofinalLimitUp
