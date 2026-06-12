import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConstructiveRealLineUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConstructiveRealLineUp : Type where
  | mk :
      (dyadicTolerance streamWindow regularReadback realSeal locatedBoundary apartnessBoundary
        densityHandoff intervalReadback transport replay provenance localName : BHist) →
        ConstructiveRealLineUp
  deriving DecidableEq

def constructiveRealLineEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: constructiveRealLineEncodeBHist h
  | BHist.e1 h => BMark.b1 :: constructiveRealLineEncodeBHist h

def constructiveRealLineDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (constructiveRealLineDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (constructiveRealLineDecodeBHist tail)

private theorem constructiveRealLineDecode_encode_bhist :
    ∀ h : BHist,
      constructiveRealLineDecodeBHist (constructiveRealLineEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem constructiveRealLine_mk_congr
    {dyadicTolerance dyadicTolerance' streamWindow streamWindow' regularReadback
      regularReadback' realSeal realSeal' locatedBoundary locatedBoundary' apartnessBoundary
      apartnessBoundary' densityHandoff densityHandoff' intervalReadback intervalReadback'
      transport transport' replay replay' provenance provenance' localName localName' : BHist}
    (hDyadicTolerance : dyadicTolerance' = dyadicTolerance)
    (hStreamWindow : streamWindow' = streamWindow)
    (hRegularReadback : regularReadback' = regularReadback)
    (hRealSeal : realSeal' = realSeal)
    (hLocatedBoundary : locatedBoundary' = locatedBoundary)
    (hApartnessBoundary : apartnessBoundary' = apartnessBoundary)
    (hDensityHandoff : densityHandoff' = densityHandoff)
    (hIntervalReadback : intervalReadback' = intervalReadback)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    ConstructiveRealLineUp.mk dyadicTolerance' streamWindow' regularReadback' realSeal'
        locatedBoundary' apartnessBoundary' densityHandoff' intervalReadback' transport'
        replay' provenance' localName' =
      ConstructiveRealLineUp.mk dyadicTolerance streamWindow regularReadback realSeal
        locatedBoundary apartnessBoundary densityHandoff intervalReadback transport replay
        provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hDyadicTolerance
  cases hStreamWindow
  cases hRegularReadback
  cases hRealSeal
  cases hLocatedBoundary
  cases hApartnessBoundary
  cases hDensityHandoff
  cases hIntervalReadback
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hLocalName
  rfl

def constructiveRealLineFields : ConstructiveRealLineUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConstructiveRealLineUp.mk dyadicTolerance streamWindow regularReadback realSeal
      locatedBoundary apartnessBoundary densityHandoff intervalReadback transport replay
      provenance localName =>
      [dyadicTolerance, streamWindow, regularReadback, realSeal, locatedBoundary,
        apartnessBoundary, densityHandoff, intervalReadback, transport, replay, provenance,
        localName]

def constructiveRealLineToEventFlow : ConstructiveRealLineUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (constructiveRealLineFields x).map constructiveRealLineEncodeBHist

def constructiveRealLineFromEventFlow : EventFlow → Option ConstructiveRealLineUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | dyadicTolerance :: rest0 =>
      match rest0 with
      | [] => none
      | streamWindow :: rest1 =>
          match rest1 with
          | [] => none
          | regularReadback :: rest2 =>
              match rest2 with
              | [] => none
              | realSeal :: rest3 =>
                  match rest3 with
                  | [] => none
                  | locatedBoundary :: rest4 =>
                      match rest4 with
                      | [] => none
                      | apartnessBoundary :: rest5 =>
                          match rest5 with
                          | [] => none
                          | densityHandoff :: rest6 =>
                              match rest6 with
                              | [] => none
                              | intervalReadback :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | transport :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | replay :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | provenance :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | localName :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (ConstructiveRealLineUp.mk
                                                          (constructiveRealLineDecodeBHist
                                                            dyadicTolerance)
                                                          (constructiveRealLineDecodeBHist
                                                            streamWindow)
                                                          (constructiveRealLineDecodeBHist
                                                            regularReadback)
                                                          (constructiveRealLineDecodeBHist
                                                            realSeal)
                                                          (constructiveRealLineDecodeBHist
                                                            locatedBoundary)
                                                          (constructiveRealLineDecodeBHist
                                                            apartnessBoundary)
                                                          (constructiveRealLineDecodeBHist
                                                            densityHandoff)
                                                          (constructiveRealLineDecodeBHist
                                                            intervalReadback)
                                                          (constructiveRealLineDecodeBHist
                                                            transport)
                                                          (constructiveRealLineDecodeBHist
                                                            replay)
                                                          (constructiveRealLineDecodeBHist
                                                            provenance)
                                                          (constructiveRealLineDecodeBHist
                                                            localName))
                                                  | _ :: _ => none

private theorem constructiveRealLine_round_trip :
    ∀ x : ConstructiveRealLineUp,
      constructiveRealLineFromEventFlow (constructiveRealLineToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk dyadicTolerance streamWindow regularReadback realSeal locatedBoundary apartnessBoundary
      densityHandoff intervalReadback transport replay provenance localName =>
      change
        some
          (ConstructiveRealLineUp.mk
            (constructiveRealLineDecodeBHist
              (constructiveRealLineEncodeBHist dyadicTolerance))
            (constructiveRealLineDecodeBHist
              (constructiveRealLineEncodeBHist streamWindow))
            (constructiveRealLineDecodeBHist
              (constructiveRealLineEncodeBHist regularReadback))
            (constructiveRealLineDecodeBHist
              (constructiveRealLineEncodeBHist realSeal))
            (constructiveRealLineDecodeBHist
              (constructiveRealLineEncodeBHist locatedBoundary))
            (constructiveRealLineDecodeBHist
              (constructiveRealLineEncodeBHist apartnessBoundary))
            (constructiveRealLineDecodeBHist
              (constructiveRealLineEncodeBHist densityHandoff))
            (constructiveRealLineDecodeBHist
              (constructiveRealLineEncodeBHist intervalReadback))
            (constructiveRealLineDecodeBHist
              (constructiveRealLineEncodeBHist transport))
            (constructiveRealLineDecodeBHist
              (constructiveRealLineEncodeBHist replay))
            (constructiveRealLineDecodeBHist
              (constructiveRealLineEncodeBHist provenance))
            (constructiveRealLineDecodeBHist
              (constructiveRealLineEncodeBHist localName))) =
          some
            (ConstructiveRealLineUp.mk dyadicTolerance streamWindow regularReadback realSeal
              locatedBoundary apartnessBoundary densityHandoff intervalReadback transport replay
              provenance localName)
      exact
        congrArg some
          (constructiveRealLine_mk_congr
            (constructiveRealLineDecode_encode_bhist dyadicTolerance)
            (constructiveRealLineDecode_encode_bhist streamWindow)
            (constructiveRealLineDecode_encode_bhist regularReadback)
            (constructiveRealLineDecode_encode_bhist realSeal)
            (constructiveRealLineDecode_encode_bhist locatedBoundary)
            (constructiveRealLineDecode_encode_bhist apartnessBoundary)
            (constructiveRealLineDecode_encode_bhist densityHandoff)
            (constructiveRealLineDecode_encode_bhist intervalReadback)
            (constructiveRealLineDecode_encode_bhist transport)
            (constructiveRealLineDecode_encode_bhist replay)
            (constructiveRealLineDecode_encode_bhist provenance)
            (constructiveRealLineDecode_encode_bhist localName))

private theorem constructiveRealLineToEventFlow_injective {x y : ConstructiveRealLineUp} :
    constructiveRealLineToEventFlow x = constructiveRealLineToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = constructiveRealLineFromEventFlow (constructiveRealLineToEventFlow x) :=
        (constructiveRealLine_round_trip x).symm
      _ = constructiveRealLineFromEventFlow (constructiveRealLineToEventFlow y) :=
        congrArg constructiveRealLineFromEventFlow hxy
      _ = some y := constructiveRealLine_round_trip y
  exact Option.some.inj optionEq

instance constructiveRealLineBHistCarrier : BHistCarrier ConstructiveRealLineUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := constructiveRealLineToEventFlow
  fromEventFlow := constructiveRealLineFromEventFlow

instance constructiveRealLineChapterTasteGate :
    ChapterTasteGate ConstructiveRealLineUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change constructiveRealLineFromEventFlow (constructiveRealLineToEventFlow x) = some x
    exact constructiveRealLine_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (constructiveRealLineToEventFlow_injective heq)

theorem ConstructiveRealLineTasteGate_single_carrier_alignment :
    (∀ h : BHist, constructiveRealLineDecodeBHist (constructiveRealLineEncodeBHist h) = h) ∧
      (∀ x : ConstructiveRealLineUp,
        constructiveRealLineFromEventFlow (constructiveRealLineToEventFlow x) = some x) ∧
        (∀ x y : ConstructiveRealLineUp,
          constructiveRealLineToEventFlow x = constructiveRealLineToEventFlow y → x = y) ∧
          constructiveRealLineEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    And.intro constructiveRealLineDecode_encode_bhist
      (And.intro constructiveRealLine_round_trip
        (And.intro
          (fun x y heq => constructiveRealLineToEventFlow_injective heq)
          rfl))

end BEDC.Derived.ConstructiveRealLineUp.TasteGate
