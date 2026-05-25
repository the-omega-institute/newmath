import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySeriesCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySeriesCriterionUp : Type where
  | mk :
      (series partialSums windows regularReadback dyadicLedger threshold realSeal transport
        replay provenance localName : BHist) ->
        CauchySeriesCriterionUp
  deriving DecidableEq

def cauchySeriesCriterionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySeriesCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySeriesCriterionEncodeBHist h

def cauchySeriesCriterionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySeriesCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySeriesCriterionDecodeBHist tail)

private theorem CauchySeriesCriterionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cauchySeriesCriterionDecodeBHist
      (cauchySeriesCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchySeriesCriterionFields : CauchySeriesCriterionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySeriesCriterionUp.mk series partialSums windows regularReadback dyadicLedger
      threshold realSeal transport replay provenance localName =>
      [series, partialSums, windows, regularReadback, dyadicLedger, threshold, realSeal,
        transport, replay, provenance, localName]

def cauchySeriesCriterionToEventFlow : CauchySeriesCriterionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchySeriesCriterionFields x).map cauchySeriesCriterionEncodeBHist

def cauchySeriesCriterionFromEventFlow : EventFlow -> Option CauchySeriesCriterionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | series :: rest0 =>
      match rest0 with
      | [] => none
      | partialSums :: rest1 =>
          match rest1 with
          | [] => none
          | windows :: rest2 =>
              match rest2 with
              | [] => none
              | regularReadback :: rest3 =>
                  match rest3 with
                  | [] => none
                  | dyadicLedger :: rest4 =>
                      match rest4 with
                      | [] => none
                      | threshold :: rest5 =>
                          match rest5 with
                          | [] => none
                          | realSeal :: rest6 =>
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
                                          | localName :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (CauchySeriesCriterionUp.mk
                                                      (cauchySeriesCriterionDecodeBHist series)
                                                      (cauchySeriesCriterionDecodeBHist
                                                        partialSums)
                                                      (cauchySeriesCriterionDecodeBHist windows)
                                                      (cauchySeriesCriterionDecodeBHist
                                                        regularReadback)
                                                      (cauchySeriesCriterionDecodeBHist
                                                        dyadicLedger)
                                                      (cauchySeriesCriterionDecodeBHist
                                                        threshold)
                                                      (cauchySeriesCriterionDecodeBHist realSeal)
                                                      (cauchySeriesCriterionDecodeBHist transport)
                                                      (cauchySeriesCriterionDecodeBHist replay)
                                                      (cauchySeriesCriterionDecodeBHist
                                                        provenance)
                                                      (cauchySeriesCriterionDecodeBHist
                                                        localName))
                                              | _ :: _ => none

private theorem CauchySeriesCriterionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchySeriesCriterionUp,
      cauchySeriesCriterionFromEventFlow (cauchySeriesCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk series partialSums windows regularReadback dyadicLedger threshold realSeal transport
      replay provenance localName =>
      change
        some
          (CauchySeriesCriterionUp.mk
            (cauchySeriesCriterionDecodeBHist (cauchySeriesCriterionEncodeBHist series))
            (cauchySeriesCriterionDecodeBHist (cauchySeriesCriterionEncodeBHist partialSums))
            (cauchySeriesCriterionDecodeBHist (cauchySeriesCriterionEncodeBHist windows))
            (cauchySeriesCriterionDecodeBHist
              (cauchySeriesCriterionEncodeBHist regularReadback))
            (cauchySeriesCriterionDecodeBHist (cauchySeriesCriterionEncodeBHist dyadicLedger))
            (cauchySeriesCriterionDecodeBHist (cauchySeriesCriterionEncodeBHist threshold))
            (cauchySeriesCriterionDecodeBHist (cauchySeriesCriterionEncodeBHist realSeal))
            (cauchySeriesCriterionDecodeBHist (cauchySeriesCriterionEncodeBHist transport))
            (cauchySeriesCriterionDecodeBHist (cauchySeriesCriterionEncodeBHist replay))
            (cauchySeriesCriterionDecodeBHist (cauchySeriesCriterionEncodeBHist provenance))
            (cauchySeriesCriterionDecodeBHist (cauchySeriesCriterionEncodeBHist localName))) =
          some
            (CauchySeriesCriterionUp.mk series partialSums windows regularReadback dyadicLedger
              threshold realSeal transport replay provenance localName)
      rw [CauchySeriesCriterionTasteGate_single_carrier_alignment_decode_encode series,
        CauchySeriesCriterionTasteGate_single_carrier_alignment_decode_encode partialSums,
        CauchySeriesCriterionTasteGate_single_carrier_alignment_decode_encode windows,
        CauchySeriesCriterionTasteGate_single_carrier_alignment_decode_encode regularReadback,
        CauchySeriesCriterionTasteGate_single_carrier_alignment_decode_encode dyadicLedger,
        CauchySeriesCriterionTasteGate_single_carrier_alignment_decode_encode threshold,
        CauchySeriesCriterionTasteGate_single_carrier_alignment_decode_encode realSeal,
        CauchySeriesCriterionTasteGate_single_carrier_alignment_decode_encode transport,
        CauchySeriesCriterionTasteGate_single_carrier_alignment_decode_encode replay,
        CauchySeriesCriterionTasteGate_single_carrier_alignment_decode_encode provenance,
        CauchySeriesCriterionTasteGate_single_carrier_alignment_decode_encode localName]

private theorem CauchySeriesCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchySeriesCriterionUp} :
    cauchySeriesCriterionToEventFlow x = cauchySeriesCriterionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySeriesCriterionFromEventFlow (cauchySeriesCriterionToEventFlow x) =
        cauchySeriesCriterionFromEventFlow (cauchySeriesCriterionToEventFlow y) :=
    congrArg cauchySeriesCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchySeriesCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchySeriesCriterionTasteGate_single_carrier_alignment_round_trip y)))

instance cauchySeriesCriterionBHistCarrier : BHistCarrier CauchySeriesCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySeriesCriterionToEventFlow
  fromEventFlow := cauchySeriesCriterionFromEventFlow

instance cauchySeriesCriterionChapterTasteGate :
    ChapterTasteGate CauchySeriesCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchySeriesCriterionFromEventFlow (cauchySeriesCriterionToEventFlow x) = some x
    exact CauchySeriesCriterionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchySeriesCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def CauchySeriesCriterionTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CauchySeriesCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchySeriesCriterionChapterTasteGate

theorem CauchySeriesCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchySeriesCriterionDecodeBHist
      (cauchySeriesCriterionEncodeBHist h) = h) ∧
      (∀ x : CauchySeriesCriterionUp,
        cauchySeriesCriterionFromEventFlow (cauchySeriesCriterionToEventFlow x) = some x) ∧
        (∀ x y : CauchySeriesCriterionUp,
          cauchySeriesCriterionToEventFlow x = cauchySeriesCriterionToEventFlow y -> x = y) ∧
          cauchySeriesCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CauchySeriesCriterionTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact CauchySeriesCriterionTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact CauchySeriesCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.CauchySeriesCriterionUp
