import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySequenceEquivalenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySequenceEquivalenceUp : Type where
  | mk :
      (leftName rightName leftWindow rightWindow tolerance equivalence sealComparison
        transport continuation provenance nameCert : BHist) →
      CauchySequenceEquivalenceUp
  deriving DecidableEq

def cauchySequenceEquivalenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySequenceEquivalenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySequenceEquivalenceEncodeBHist h

def cauchySequenceEquivalenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySequenceEquivalenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySequenceEquivalenceDecodeBHist tail)

private theorem CauchySequenceEquivalenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchySequenceEquivalenceDecodeBHist
        (cauchySequenceEquivalenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchySequenceEquivalenceToEventFlow :
    CauchySequenceEquivalenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySequenceEquivalenceUp.mk leftName rightName leftWindow rightWindow tolerance
      equivalence sealComparison transport continuation provenance nameCert =>
      [[BMark.b0],
        cauchySequenceEquivalenceEncodeBHist leftName,
        [BMark.b1, BMark.b0],
        cauchySequenceEquivalenceEncodeBHist rightName,
        [BMark.b1, BMark.b1, BMark.b0],
        cauchySequenceEquivalenceEncodeBHist leftWindow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchySequenceEquivalenceEncodeBHist rightWindow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchySequenceEquivalenceEncodeBHist tolerance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchySequenceEquivalenceEncodeBHist equivalence,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchySequenceEquivalenceEncodeBHist sealComparison,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cauchySequenceEquivalenceEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        cauchySequenceEquivalenceEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        cauchySequenceEquivalenceEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchySequenceEquivalenceEncodeBHist nameCert]

def cauchySequenceEquivalenceFromEventFlow :
    EventFlow → Option CauchySequenceEquivalenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | leftName :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | rightName :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | leftWindow :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | rightWindow :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | tolerance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | equivalence :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | sealComparison :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | transport :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | continuation :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | provenance :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | nameCert :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (CauchySequenceEquivalenceUp.mk
                                                                                                  (cauchySequenceEquivalenceDecodeBHist leftName)
                                                                                                  (cauchySequenceEquivalenceDecodeBHist rightName)
                                                                                                  (cauchySequenceEquivalenceDecodeBHist leftWindow)
                                                                                                  (cauchySequenceEquivalenceDecodeBHist rightWindow)
                                                                                                  (cauchySequenceEquivalenceDecodeBHist tolerance)
                                                                                                  (cauchySequenceEquivalenceDecodeBHist equivalence)
                                                                                                  (cauchySequenceEquivalenceDecodeBHist sealComparison)
                                                                                                  (cauchySequenceEquivalenceDecodeBHist transport)
                                                                                                  (cauchySequenceEquivalenceDecodeBHist continuation)
                                                                                                  (cauchySequenceEquivalenceDecodeBHist provenance)
                                                                                                  (cauchySequenceEquivalenceDecodeBHist nameCert))
                                                                                          | _ :: _ => none

private theorem cauchySequenceEquivalence_round_trip :
    ∀ x : CauchySequenceEquivalenceUp,
      cauchySequenceEquivalenceFromEventFlow
        (cauchySequenceEquivalenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk leftName rightName leftWindow rightWindow tolerance equivalence sealComparison
      transport continuation provenance nameCert =>
      change
        some
          (CauchySequenceEquivalenceUp.mk
            (cauchySequenceEquivalenceDecodeBHist
              (cauchySequenceEquivalenceEncodeBHist leftName))
            (cauchySequenceEquivalenceDecodeBHist
              (cauchySequenceEquivalenceEncodeBHist rightName))
            (cauchySequenceEquivalenceDecodeBHist
              (cauchySequenceEquivalenceEncodeBHist leftWindow))
            (cauchySequenceEquivalenceDecodeBHist
              (cauchySequenceEquivalenceEncodeBHist rightWindow))
            (cauchySequenceEquivalenceDecodeBHist
              (cauchySequenceEquivalenceEncodeBHist tolerance))
            (cauchySequenceEquivalenceDecodeBHist
              (cauchySequenceEquivalenceEncodeBHist equivalence))
            (cauchySequenceEquivalenceDecodeBHist
              (cauchySequenceEquivalenceEncodeBHist sealComparison))
            (cauchySequenceEquivalenceDecodeBHist
              (cauchySequenceEquivalenceEncodeBHist transport))
            (cauchySequenceEquivalenceDecodeBHist
              (cauchySequenceEquivalenceEncodeBHist continuation))
            (cauchySequenceEquivalenceDecodeBHist
              (cauchySequenceEquivalenceEncodeBHist provenance))
            (cauchySequenceEquivalenceDecodeBHist
              (cauchySequenceEquivalenceEncodeBHist nameCert))) =
          some
            (CauchySequenceEquivalenceUp.mk leftName rightName leftWindow rightWindow
              tolerance equivalence sealComparison transport continuation provenance nameCert)
      have hLeftName :=
        CauchySequenceEquivalenceTasteGate_single_carrier_alignment_decode_encode leftName
      have hRightName :=
        CauchySequenceEquivalenceTasteGate_single_carrier_alignment_decode_encode rightName
      have hLeftWindow :=
        CauchySequenceEquivalenceTasteGate_single_carrier_alignment_decode_encode leftWindow
      have hRightWindow :=
        CauchySequenceEquivalenceTasteGate_single_carrier_alignment_decode_encode rightWindow
      have hTolerance :=
        CauchySequenceEquivalenceTasteGate_single_carrier_alignment_decode_encode tolerance
      have hEquivalence :=
        CauchySequenceEquivalenceTasteGate_single_carrier_alignment_decode_encode equivalence
      have hSealComparison :=
        CauchySequenceEquivalenceTasteGate_single_carrier_alignment_decode_encode sealComparison
      have hTransport :=
        CauchySequenceEquivalenceTasteGate_single_carrier_alignment_decode_encode transport
      have hContinuation :=
        CauchySequenceEquivalenceTasteGate_single_carrier_alignment_decode_encode continuation
      have hProvenance :=
        CauchySequenceEquivalenceTasteGate_single_carrier_alignment_decode_encode provenance
      have hNameCert :=
        CauchySequenceEquivalenceTasteGate_single_carrier_alignment_decode_encode nameCert
      rw [hLeftName, hRightName, hLeftWindow, hRightWindow, hTolerance, hEquivalence,
        hSealComparison, hTransport, hContinuation, hProvenance, hNameCert]

private theorem cauchySequenceEquivalenceToEventFlow_injective
    {x y : CauchySequenceEquivalenceUp} :
    cauchySequenceEquivalenceToEventFlow x =
      cauchySequenceEquivalenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySequenceEquivalenceFromEventFlow
          (cauchySequenceEquivalenceToEventFlow x) =
        cauchySequenceEquivalenceFromEventFlow
          (cauchySequenceEquivalenceToEventFlow y) :=
    congrArg cauchySequenceEquivalenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchySequenceEquivalence_round_trip x).symm
      (Eq.trans hread (cauchySequenceEquivalence_round_trip y)))

instance cauchySequenceEquivalenceBHistCarrier :
    BHistCarrier CauchySequenceEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySequenceEquivalenceToEventFlow
  fromEventFlow := cauchySequenceEquivalenceFromEventFlow

instance cauchySequenceEquivalenceChapterTasteGate :
    ChapterTasteGate CauchySequenceEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchySequenceEquivalenceFromEventFlow
        (cauchySequenceEquivalenceToEventFlow x) = some x
    exact cauchySequenceEquivalence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchySequenceEquivalenceToEventFlow_injective heq)

theorem CauchySequenceEquivalenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchySequenceEquivalenceDecodeBHist
        (cauchySequenceEquivalenceEncodeBHist h) = h) ∧
      (∀ x : CauchySequenceEquivalenceUp,
        cauchySequenceEquivalenceFromEventFlow
          (cauchySequenceEquivalenceToEventFlow x) = some x) ∧
        (∀ x y : CauchySequenceEquivalenceUp,
          cauchySequenceEquivalenceToEventFlow x =
            cauchySequenceEquivalenceToEventFlow y → x = y) ∧
          cauchySequenceEquivalenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CauchySequenceEquivalenceTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact cauchySequenceEquivalence_round_trip
    · constructor
      · intro x y heq
        exact cauchySequenceEquivalenceToEventFlow_injective heq
      · rfl

end BEDC.Derived.CauchySequenceEquivalenceUp
