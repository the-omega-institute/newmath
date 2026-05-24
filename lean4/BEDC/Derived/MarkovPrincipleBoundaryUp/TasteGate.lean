import BEDC.Derived.MarkovPrincipleBoundaryUp
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MarkovPrincipleBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def markovPrincipleBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: markovPrincipleBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: markovPrincipleBoundaryEncodeBHist h

def markovPrincipleBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (markovPrincipleBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (markovPrincipleBoundaryDecodeBHist tail)

theorem MarkovPrincipleBoundaryUpTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, markovPrincipleBoundaryDecodeBHist
      (markovPrincipleBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def markovPrincipleBoundaryFields : MarkovPrincipleBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MarkovPrincipleBoundaryUp.mk inspection speckerControl streamSchedule rationalReadback
      dyadicLedger realSeal witnessRow transport replay provenance name =>
      [inspection, speckerControl, streamSchedule, rationalReadback, dyadicLedger, realSeal,
        witnessRow, transport, replay, provenance, name]

def markovPrincipleBoundaryToEventFlow : MarkovPrincipleBoundaryUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (markovPrincipleBoundaryFields x).map markovPrincipleBoundaryEncodeBHist

def markovPrincipleBoundaryFromEventFlow :
    EventFlow → Option MarkovPrincipleBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | inspection :: rest0 =>
      match rest0 with
      | [] => none
      | speckerControl :: rest1 =>
          match rest1 with
          | [] => none
          | streamSchedule :: rest2 =>
              match rest2 with
              | [] => none
              | rationalReadback :: rest3 =>
                  match rest3 with
                  | [] => none
                  | dyadicLedger :: rest4 =>
                      match rest4 with
                      | [] => none
                      | realSeal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | witnessRow :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | replay :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | provenance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | name :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (MarkovPrincipleBoundaryUp.mk
                                                      (markovPrincipleBoundaryDecodeBHist
                                                        inspection)
                                                      (markovPrincipleBoundaryDecodeBHist
                                                        speckerControl)
                                                      (markovPrincipleBoundaryDecodeBHist
                                                        streamSchedule)
                                                      (markovPrincipleBoundaryDecodeBHist
                                                        rationalReadback)
                                                      (markovPrincipleBoundaryDecodeBHist
                                                        dyadicLedger)
                                                      (markovPrincipleBoundaryDecodeBHist
                                                        realSeal)
                                                      (markovPrincipleBoundaryDecodeBHist
                                                        witnessRow)
                                                      (markovPrincipleBoundaryDecodeBHist
                                                        transport)
                                                      (markovPrincipleBoundaryDecodeBHist
                                                        replay)
                                                      (markovPrincipleBoundaryDecodeBHist
                                                        provenance)
                                                      (markovPrincipleBoundaryDecodeBHist
                                                        name))
                                              | _ :: _ => none

theorem MarkovPrincipleBoundaryUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MarkovPrincipleBoundaryUp,
      markovPrincipleBoundaryFromEventFlow (markovPrincipleBoundaryToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk inspection speckerControl streamSchedule rationalReadback dyadicLedger realSeal
      witnessRow transport replay provenance name =>
      change
        some
          (MarkovPrincipleBoundaryUp.mk
            (markovPrincipleBoundaryDecodeBHist
              (markovPrincipleBoundaryEncodeBHist inspection))
            (markovPrincipleBoundaryDecodeBHist
              (markovPrincipleBoundaryEncodeBHist speckerControl))
            (markovPrincipleBoundaryDecodeBHist
              (markovPrincipleBoundaryEncodeBHist streamSchedule))
            (markovPrincipleBoundaryDecodeBHist
              (markovPrincipleBoundaryEncodeBHist rationalReadback))
            (markovPrincipleBoundaryDecodeBHist
              (markovPrincipleBoundaryEncodeBHist dyadicLedger))
            (markovPrincipleBoundaryDecodeBHist
              (markovPrincipleBoundaryEncodeBHist realSeal))
            (markovPrincipleBoundaryDecodeBHist
              (markovPrincipleBoundaryEncodeBHist witnessRow))
            (markovPrincipleBoundaryDecodeBHist
              (markovPrincipleBoundaryEncodeBHist transport))
            (markovPrincipleBoundaryDecodeBHist
              (markovPrincipleBoundaryEncodeBHist replay))
            (markovPrincipleBoundaryDecodeBHist
              (markovPrincipleBoundaryEncodeBHist provenance))
            (markovPrincipleBoundaryDecodeBHist
              (markovPrincipleBoundaryEncodeBHist name))) =
          some
            (MarkovPrincipleBoundaryUp.mk inspection speckerControl streamSchedule
              rationalReadback dyadicLedger realSeal witnessRow transport replay provenance name)
      rw [MarkovPrincipleBoundaryUpTasteGate_single_carrier_alignment_decode inspection,
        MarkovPrincipleBoundaryUpTasteGate_single_carrier_alignment_decode speckerControl,
        MarkovPrincipleBoundaryUpTasteGate_single_carrier_alignment_decode streamSchedule,
        MarkovPrincipleBoundaryUpTasteGate_single_carrier_alignment_decode rationalReadback,
        MarkovPrincipleBoundaryUpTasteGate_single_carrier_alignment_decode dyadicLedger,
        MarkovPrincipleBoundaryUpTasteGate_single_carrier_alignment_decode realSeal,
        MarkovPrincipleBoundaryUpTasteGate_single_carrier_alignment_decode witnessRow,
        MarkovPrincipleBoundaryUpTasteGate_single_carrier_alignment_decode transport,
        MarkovPrincipleBoundaryUpTasteGate_single_carrier_alignment_decode replay,
        MarkovPrincipleBoundaryUpTasteGate_single_carrier_alignment_decode provenance,
        MarkovPrincipleBoundaryUpTasteGate_single_carrier_alignment_decode name]

theorem MarkovPrincipleBoundaryUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MarkovPrincipleBoundaryUp} :
    markovPrincipleBoundaryToEventFlow x = markovPrincipleBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      markovPrincipleBoundaryFromEventFlow (markovPrincipleBoundaryToEventFlow x) =
        markovPrincipleBoundaryFromEventFlow (markovPrincipleBoundaryToEventFlow y) :=
    congrArg markovPrincipleBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MarkovPrincipleBoundaryUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MarkovPrincipleBoundaryUpTasteGate_single_carrier_alignment_round_trip y)))

instance markovPrincipleBoundaryBHistCarrier : BHistCarrier MarkovPrincipleBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := markovPrincipleBoundaryToEventFlow
  fromEventFlow := markovPrincipleBoundaryFromEventFlow

instance markovPrincipleBoundaryChapterTasteGate :
    ChapterTasteGate MarkovPrincipleBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change markovPrincipleBoundaryFromEventFlow (markovPrincipleBoundaryToEventFlow x) =
      some x
    exact MarkovPrincipleBoundaryUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MarkovPrincipleBoundaryUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate MarkovPrincipleBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  markovPrincipleBoundaryChapterTasteGate

theorem MarkovPrincipleBoundaryUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, markovPrincipleBoundaryDecodeBHist
      (markovPrincipleBoundaryEncodeBHist h) = h) ∧
      (∀ x : MarkovPrincipleBoundaryUp,
        markovPrincipleBoundaryFromEventFlow (markovPrincipleBoundaryToEventFlow x) =
          some x) ∧
        (∀ x y : MarkovPrincipleBoundaryUp,
          markovPrincipleBoundaryToEventFlow x = markovPrincipleBoundaryToEventFlow y →
            x = y) ∧
          markovPrincipleBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact MarkovPrincipleBoundaryUpTasteGate_single_carrier_alignment_decode
  · constructor
    · exact MarkovPrincipleBoundaryUpTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact MarkovPrincipleBoundaryUpTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.MarkovPrincipleBoundaryUp
