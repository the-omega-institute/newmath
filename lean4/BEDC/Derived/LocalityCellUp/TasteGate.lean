import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocalityCellUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocalityCellUp : Type where
  | mk :
      (observerLeft observerRight recordLeft recordRight gapLeft gapRight transport route package name :
        BHist) →
        LocalityCellUp
  deriving DecidableEq

def localityCellEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: localityCellEncodeBHist h
  | BHist.e1 h => BMark.b1 :: localityCellEncodeBHist h

def localityCellDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (localityCellDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (localityCellDecodeBHist tail)

private theorem localityCellDecode_encode_bhist :
    ∀ h : BHist, localityCellDecodeBHist (localityCellEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem localityCell_mk_congr
    {observerLeft observerLeft' observerRight observerRight' recordLeft recordLeft'
      recordRight recordRight' gapLeft gapLeft' gapRight gapRight' transport transport'
      route route' package package' name name' : BHist}
    (hObserverLeft : observerLeft' = observerLeft)
    (hObserverRight : observerRight' = observerRight)
    (hRecordLeft : recordLeft' = recordLeft)
    (hRecordRight : recordRight' = recordRight)
    (hGapLeft : gapLeft' = gapLeft)
    (hGapRight : gapRight' = gapRight)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hPackage : package' = package)
    (hName : name' = name) :
    LocalityCellUp.mk observerLeft' observerRight' recordLeft' recordRight' gapLeft' gapRight'
        transport' route' package' name' =
      LocalityCellUp.mk observerLeft observerRight recordLeft recordRight gapLeft gapRight
        transport route package name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hObserverLeft
  cases hObserverRight
  cases hRecordLeft
  cases hRecordRight
  cases hGapLeft
  cases hGapRight
  cases hTransport
  cases hRoute
  cases hPackage
  cases hName
  rfl

def localityCellToEventFlow : LocalityCellUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocalityCellUp.mk observerLeft observerRight recordLeft recordRight gapLeft gapRight transport
      route package name =>
      [[BMark.b0],
        localityCellEncodeBHist observerLeft,
        [BMark.b1, BMark.b0],
        localityCellEncodeBHist observerRight,
        [BMark.b1, BMark.b1, BMark.b0],
        localityCellEncodeBHist recordLeft,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        localityCellEncodeBHist recordRight,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        localityCellEncodeBHist gapLeft,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        localityCellEncodeBHist gapRight,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        localityCellEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        localityCellEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        localityCellEncodeBHist package,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        localityCellEncodeBHist name]

def localityCellFromEventFlow : EventFlow → Option LocalityCellUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | observerLeft :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | observerRight :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | recordLeft :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | recordRight :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | gapLeft :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | gapRight :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | route :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | package :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | name :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (LocalityCellUp.mk
                                                                                          (localityCellDecodeBHist
                                                                                            observerLeft)
                                                                                          (localityCellDecodeBHist
                                                                                            observerRight)
                                                                                          (localityCellDecodeBHist
                                                                                            recordLeft)
                                                                                          (localityCellDecodeBHist
                                                                                            recordRight)
                                                                                          (localityCellDecodeBHist
                                                                                            gapLeft)
                                                                                          (localityCellDecodeBHist
                                                                                            gapRight)
                                                                                          (localityCellDecodeBHist
                                                                                            transport)
                                                                                          (localityCellDecodeBHist
                                                                                            route)
                                                                                          (localityCellDecodeBHist
                                                                                            package)
                                                                                          (localityCellDecodeBHist
                                                                                            name))
                                                                                  | _ :: _ => none

private theorem localityCell_round_trip :
    ∀ x : LocalityCellUp, localityCellFromEventFlow (localityCellToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk observerLeft observerRight recordLeft recordRight gapLeft gapRight transport route package name =>
      change
        some
            (LocalityCellUp.mk
              (localityCellDecodeBHist (localityCellEncodeBHist observerLeft))
              (localityCellDecodeBHist (localityCellEncodeBHist observerRight))
              (localityCellDecodeBHist (localityCellEncodeBHist recordLeft))
              (localityCellDecodeBHist (localityCellEncodeBHist recordRight))
              (localityCellDecodeBHist (localityCellEncodeBHist gapLeft))
              (localityCellDecodeBHist (localityCellEncodeBHist gapRight))
              (localityCellDecodeBHist (localityCellEncodeBHist transport))
              (localityCellDecodeBHist (localityCellEncodeBHist route))
              (localityCellDecodeBHist (localityCellEncodeBHist package))
              (localityCellDecodeBHist (localityCellEncodeBHist name))) =
          some
            (LocalityCellUp.mk observerLeft observerRight recordLeft recordRight gapLeft gapRight
              transport route package name)
      exact
        congrArg some
          (localityCell_mk_congr
            (localityCellDecode_encode_bhist observerLeft)
            (localityCellDecode_encode_bhist observerRight)
            (localityCellDecode_encode_bhist recordLeft)
            (localityCellDecode_encode_bhist recordRight)
            (localityCellDecode_encode_bhist gapLeft)
            (localityCellDecode_encode_bhist gapRight)
            (localityCellDecode_encode_bhist transport)
            (localityCellDecode_encode_bhist route)
            (localityCellDecode_encode_bhist package)
            (localityCellDecode_encode_bhist name))

private theorem localityCellToEventFlow_injective {x y : LocalityCellUp} :
    localityCellToEventFlow x = localityCellToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      localityCellFromEventFlow (localityCellToEventFlow x) =
        localityCellFromEventFlow (localityCellToEventFlow y) :=
    congrArg localityCellFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (localityCell_round_trip x).symm
      (Eq.trans hread (localityCell_round_trip y)))

instance localityCellBHistCarrier : BHistCarrier LocalityCellUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := localityCellToEventFlow
  fromEventFlow := localityCellFromEventFlow

instance localityCellChapterTasteGate : ChapterTasteGate LocalityCellUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change localityCellFromEventFlow (localityCellToEventFlow x) = some x
    exact localityCell_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (localityCellToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocalityCellUp :=
  -- BEDC touchpoint anchor: BHist BMark
  localityCellChapterTasteGate

theorem LocalityCellTasteGate_single_carrier_alignment :
    (∀ h : BHist, localityCellDecodeBHist (localityCellEncodeBHist h) = h) ∧
      (∀ x : LocalityCellUp, localityCellFromEventFlow (localityCellToEventFlow x) = some x) ∧
        (∀ x y : LocalityCellUp,
          localityCellToEventFlow x = localityCellToEventFlow y → x = y) ∧
          localityCellEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact localityCellDecode_encode_bhist
  · constructor
    · exact localityCell_round_trip
    · constructor
      · intro x y heq
        exact localityCellToEventFlow_injective heq
      · rfl

end BEDC.Derived.LocalityCellUp
