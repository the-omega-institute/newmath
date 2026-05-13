import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObservableCauchySealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObservableCauchySealUp : Type where
  | mk :
      (precision window dyadic handoff sealRow transport route provenance name : BHist) →
        ObservableCauchySealUp
  deriving DecidableEq

def observableCauchySealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observableCauchySealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observableCauchySealEncodeBHist h

def observableCauchySealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observableCauchySealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observableCauchySealDecodeBHist tail)

private theorem ObservableCauchySealTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      observableCauchySealDecodeBHist (observableCauchySealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def observableCauchySealToEventFlow : ObservableCauchySealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObservableCauchySealUp.mk precision window dyadic handoff sealRow transport route
      provenance name =>
      [[BMark.b0],
        observableCauchySealEncodeBHist precision,
        [BMark.b1, BMark.b0],
        observableCauchySealEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b0],
        observableCauchySealEncodeBHist dyadic,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observableCauchySealEncodeBHist handoff,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observableCauchySealEncodeBHist sealRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observableCauchySealEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observableCauchySealEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        observableCauchySealEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        observableCauchySealEncodeBHist name]

def observableCauchySealFromEventFlow :
    EventFlow → Option ObservableCauchySealUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | precision :: rest1 =>
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
                      | dyadic :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | handoff :: rest7 =>
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
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (ObservableCauchySealUp.mk
                                                                                  (observableCauchySealDecodeBHist
                                                                                    precision)
                                                                                  (observableCauchySealDecodeBHist
                                                                                    window)
                                                                                  (observableCauchySealDecodeBHist
                                                                                    dyadic)
                                                                                  (observableCauchySealDecodeBHist
                                                                                    handoff)
                                                                                  (observableCauchySealDecodeBHist
                                                                                    sealRow)
                                                                                  (observableCauchySealDecodeBHist
                                                                                    transport)
                                                                                  (observableCauchySealDecodeBHist
                                                                                    route)
                                                                                  (observableCauchySealDecodeBHist
                                                                                    provenance)
                                                                                  (observableCauchySealDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem ObservableCauchySealTasteGate_single_carrier_alignment_round :
    ∀ x : ObservableCauchySealUp,
      observableCauchySealFromEventFlow
        (observableCauchySealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk precision window dyadic handoff sealRow transport route provenance name =>
      change
        some
          (ObservableCauchySealUp.mk
            (observableCauchySealDecodeBHist (observableCauchySealEncodeBHist precision))
            (observableCauchySealDecodeBHist (observableCauchySealEncodeBHist window))
            (observableCauchySealDecodeBHist (observableCauchySealEncodeBHist dyadic))
            (observableCauchySealDecodeBHist (observableCauchySealEncodeBHist handoff))
            (observableCauchySealDecodeBHist (observableCauchySealEncodeBHist sealRow))
            (observableCauchySealDecodeBHist (observableCauchySealEncodeBHist transport))
            (observableCauchySealDecodeBHist (observableCauchySealEncodeBHist route))
            (observableCauchySealDecodeBHist (observableCauchySealEncodeBHist provenance))
            (observableCauchySealDecodeBHist (observableCauchySealEncodeBHist name))) =
          some
            (ObservableCauchySealUp.mk precision window dyadic handoff sealRow transport route
              provenance name)
      rw [ObservableCauchySealTasteGate_single_carrier_alignment_decode precision,
        ObservableCauchySealTasteGate_single_carrier_alignment_decode window,
        ObservableCauchySealTasteGate_single_carrier_alignment_decode dyadic,
        ObservableCauchySealTasteGate_single_carrier_alignment_decode handoff,
        ObservableCauchySealTasteGate_single_carrier_alignment_decode sealRow,
        ObservableCauchySealTasteGate_single_carrier_alignment_decode transport,
        ObservableCauchySealTasteGate_single_carrier_alignment_decode route,
        ObservableCauchySealTasteGate_single_carrier_alignment_decode provenance,
        ObservableCauchySealTasteGate_single_carrier_alignment_decode name]

private theorem ObservableCauchySealTasteGate_single_carrier_alignment_injective
    {x y : ObservableCauchySealUp} :
    observableCauchySealToEventFlow x = observableCauchySealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observableCauchySealFromEventFlow (observableCauchySealToEventFlow x) =
        observableCauchySealFromEventFlow (observableCauchySealToEventFlow y) :=
    congrArg observableCauchySealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ObservableCauchySealTasteGate_single_carrier_alignment_round x).symm
      (Eq.trans hread (ObservableCauchySealTasteGate_single_carrier_alignment_round y)))

instance observableCauchySealBHistCarrier :
    BHistCarrier ObservableCauchySealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observableCauchySealToEventFlow
  fromEventFlow := observableCauchySealFromEventFlow

instance observableCauchySealChapterTasteGate :
    ChapterTasteGate ObservableCauchySealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change observableCauchySealFromEventFlow (observableCauchySealToEventFlow x) = some x
    exact ObservableCauchySealTasteGate_single_carrier_alignment_round x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ObservableCauchySealTasteGate_single_carrier_alignment_injective heq)

instance observableCauchySealFieldFaithful :
    FieldFaithful ObservableCauchySealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ObservableCauchySealUp.mk precision window dyadic handoff sealRow transport route
        provenance name =>
        [precision, window, dyadic, handoff, sealRow, transport, route, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk precision1 window1 dyadic1 handoff1 seal1 transport1 route1 provenance1 name1 =>
        cases y with
        | mk precision2 window2 dyadic2 handoff2 seal2 transport2 route2 provenance2 name2 =>
            injection h with hPrecision t1
            injection t1 with hWindow t2
            injection t2 with hDyadic t3
            injection t3 with hHandoff t4
            injection t4 with hSeal t5
            injection t5 with hTransport t6
            injection t6 with hRoute t7
            injection t7 with hProvenance t8
            injection t8 with hName _
            cases hPrecision
            cases hWindow
            cases hDyadic
            cases hHandoff
            cases hSeal
            cases hTransport
            cases hRoute
            cases hProvenance
            cases hName
            rfl

theorem ObservableCauchySealTasteGate_single_carrier_alignment :
    (forall h : BHist, observableCauchySealDecodeBHist
      (observableCauchySealEncodeBHist h) = h) /\
      (forall x : ObservableCauchySealUp, observableCauchySealFromEventFlow
        (observableCauchySealToEventFlow x) = some x) /\
        (forall x y : ObservableCauchySealUp, observableCauchySealToEventFlow x =
          observableCauchySealToEventFlow y -> x = y) /\
          observableCauchySealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ObservableCauchySealTasteGate_single_carrier_alignment_decode
  · constructor
    · exact ObservableCauchySealTasteGate_single_carrier_alignment_round
    · constructor
      · intro x y heq
        exact ObservableCauchySealTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.ObservableCauchySealUp
