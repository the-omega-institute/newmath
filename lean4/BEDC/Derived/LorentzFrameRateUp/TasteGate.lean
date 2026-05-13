import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LorentzFrameRateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LorentzFrameRateUp : Type where
  | mk :
      (multiHist crossHist maxRate symmetry transport continuation provenance name : BHist) →
      LorentzFrameRateUp
  deriving DecidableEq

private def lorentzFrameRateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lorentzFrameRateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lorentzFrameRateEncodeBHist h

private def lorentzFrameRateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lorentzFrameRateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lorentzFrameRateDecodeBHist tail)

private theorem lorentzFrameRateDecode_encode_bhist :
    ∀ h : BHist, lorentzFrameRateDecodeBHist (lorentzFrameRateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem lorentzFrameRate_mk_congr
    {multiHist multiHist' crossHist crossHist' maxRate maxRate' symmetry symmetry'
      transport transport' continuation continuation' provenance provenance' name name' : BHist}
    (hMultiHist : multiHist' = multiHist)
    (hCrossHist : crossHist' = crossHist)
    (hMaxRate : maxRate' = maxRate)
    (hSymmetry : symmetry' = symmetry)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    LorentzFrameRateUp.mk multiHist' crossHist' maxRate' symmetry' transport'
        continuation' provenance' name' =
      LorentzFrameRateUp.mk multiHist crossHist maxRate symmetry transport continuation
        provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hMultiHist
  cases hCrossHist
  cases hMaxRate
  cases hSymmetry
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hName
  rfl

private def lorentzFrameRateToEventFlow : LorentzFrameRateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LorentzFrameRateUp.mk multiHist crossHist maxRate symmetry transport continuation
      provenance name =>
      [[BMark.b0],
        lorentzFrameRateEncodeBHist multiHist,
        [BMark.b1, BMark.b0],
        lorentzFrameRateEncodeBHist crossHist,
        [BMark.b1, BMark.b1, BMark.b0],
        lorentzFrameRateEncodeBHist maxRate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        lorentzFrameRateEncodeBHist symmetry,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        lorentzFrameRateEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        lorentzFrameRateEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        lorentzFrameRateEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        lorentzFrameRateEncodeBHist name]

private def lorentzFrameRateFromEventFlow : EventFlow → Option LorentzFrameRateUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | multiHist :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | crossHist :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | maxRate :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | symmetry :: rest7 =>
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
                                                              | name :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (LorentzFrameRateUp.mk
                                                                          (lorentzFrameRateDecodeBHist multiHist)
                                                                          (lorentzFrameRateDecodeBHist crossHist)
                                                                          (lorentzFrameRateDecodeBHist maxRate)
                                                                          (lorentzFrameRateDecodeBHist symmetry)
                                                                          (lorentzFrameRateDecodeBHist transport)
                                                                          (lorentzFrameRateDecodeBHist continuation)
                                                                          (lorentzFrameRateDecodeBHist provenance)
                                                                          (lorentzFrameRateDecodeBHist name))
                                                                  | _ :: _ => none

private theorem lorentzFrameRate_round_trip :
    ∀ x : LorentzFrameRateUp,
      lorentzFrameRateFromEventFlow (lorentzFrameRateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk multiHist crossHist maxRate symmetry transport continuation provenance name =>
      change
        some
          (LorentzFrameRateUp.mk
            (lorentzFrameRateDecodeBHist (lorentzFrameRateEncodeBHist multiHist))
            (lorentzFrameRateDecodeBHist (lorentzFrameRateEncodeBHist crossHist))
            (lorentzFrameRateDecodeBHist (lorentzFrameRateEncodeBHist maxRate))
            (lorentzFrameRateDecodeBHist (lorentzFrameRateEncodeBHist symmetry))
            (lorentzFrameRateDecodeBHist (lorentzFrameRateEncodeBHist transport))
            (lorentzFrameRateDecodeBHist (lorentzFrameRateEncodeBHist continuation))
            (lorentzFrameRateDecodeBHist (lorentzFrameRateEncodeBHist provenance))
            (lorentzFrameRateDecodeBHist (lorentzFrameRateEncodeBHist name))) =
          some
            (LorentzFrameRateUp.mk multiHist crossHist maxRate symmetry transport
              continuation provenance name)
      exact
        congrArg some
          (lorentzFrameRate_mk_congr
            (lorentzFrameRateDecode_encode_bhist multiHist)
            (lorentzFrameRateDecode_encode_bhist crossHist)
            (lorentzFrameRateDecode_encode_bhist maxRate)
            (lorentzFrameRateDecode_encode_bhist symmetry)
            (lorentzFrameRateDecode_encode_bhist transport)
            (lorentzFrameRateDecode_encode_bhist continuation)
            (lorentzFrameRateDecode_encode_bhist provenance)
            (lorentzFrameRateDecode_encode_bhist name))

private theorem lorentzFrameRateToEventFlow_injective {x y : LorentzFrameRateUp} :
    lorentzFrameRateToEventFlow x = lorentzFrameRateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lorentzFrameRateFromEventFlow (lorentzFrameRateToEventFlow x) =
        lorentzFrameRateFromEventFlow (lorentzFrameRateToEventFlow y) :=
    congrArg lorentzFrameRateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (lorentzFrameRate_round_trip x).symm
      (Eq.trans hread (lorentzFrameRate_round_trip y)))

instance lorentzFrameRateBHistCarrier : BHistCarrier LorentzFrameRateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lorentzFrameRateToEventFlow
  fromEventFlow := lorentzFrameRateFromEventFlow

instance lorentzFrameRateChapterTasteGate : ChapterTasteGate LorentzFrameRateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lorentzFrameRateFromEventFlow (lorentzFrameRateToEventFlow x) = some x
    exact lorentzFrameRate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (lorentzFrameRateToEventFlow_injective heq)

theorem LorentzFrameRateTasteGate_single_carrier_alignment :
    (∀ h : BHist, lorentzFrameRateDecodeBHist (lorentzFrameRateEncodeBHist h) = h) ∧
      (∀ x : LorentzFrameRateUp,
        lorentzFrameRateFromEventFlow (lorentzFrameRateToEventFlow x) = some x) ∧
        (∀ x y : LorentzFrameRateUp,
          lorentzFrameRateToEventFlow x = lorentzFrameRateToEventFlow y → x = y) ∧
          lorentzFrameRateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact lorentzFrameRateDecode_encode_bhist
  · constructor
    · exact lorentzFrameRate_round_trip
    · constructor
      · intro x y heq
        exact lorentzFrameRateToEventFlow_injective heq
      · rfl

end BEDC.Derived.LorentzFrameRateUp
