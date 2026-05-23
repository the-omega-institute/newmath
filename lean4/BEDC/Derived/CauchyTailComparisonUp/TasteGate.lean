import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyTailComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyTailComparisonUp : Type where
  | mk :
      (leftName rightName modulus window endpointLedger readback provenance namecert endpoint :
        BHist) →
      CauchyTailComparisonUp

def cauchyTailComparisonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyTailComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyTailComparisonEncodeBHist h

def cauchyTailComparisonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyTailComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyTailComparisonDecodeBHist tail)

private theorem cauchyTailComparisonDecode_encode_bhist :
    ∀ h : BHist,
      cauchyTailComparisonDecodeBHist (cauchyTailComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyTailComparisonToEventFlow : CauchyTailComparisonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyTailComparisonUp.mk leftName rightName modulus window endpointLedger readback
      provenance namecert endpoint =>
      [[BMark.b0],
        cauchyTailComparisonEncodeBHist leftName,
        [BMark.b1, BMark.b0],
        cauchyTailComparisonEncodeBHist rightName,
        [BMark.b1, BMark.b1, BMark.b0],
        cauchyTailComparisonEncodeBHist modulus,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyTailComparisonEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyTailComparisonEncodeBHist endpointLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyTailComparisonEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyTailComparisonEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cauchyTailComparisonEncodeBHist namecert,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        cauchyTailComparisonEncodeBHist endpoint]

def cauchyTailComparisonFromEventFlow : EventFlow → Option CauchyTailComparisonUp
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
                      | modulus :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | window :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | endpointLedger :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | readback :: rest11 =>
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
                                                              | namecert :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | endpoint :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (CauchyTailComparisonUp.mk
                                                                                  (cauchyTailComparisonDecodeBHist leftName)
                                                                                  (cauchyTailComparisonDecodeBHist rightName)
                                                                                  (cauchyTailComparisonDecodeBHist modulus)
                                                                                  (cauchyTailComparisonDecodeBHist window)
                                                                                  (cauchyTailComparisonDecodeBHist endpointLedger)
                                                                                  (cauchyTailComparisonDecodeBHist readback)
                                                                                  (cauchyTailComparisonDecodeBHist provenance)
                                                                                  (cauchyTailComparisonDecodeBHist namecert)
                                                                                  (cauchyTailComparisonDecodeBHist endpoint))
                                                                          | _ :: _ => none

private theorem cauchyTailComparison_round_trip :
    ∀ x : CauchyTailComparisonUp,
      cauchyTailComparisonFromEventFlow
        (cauchyTailComparisonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk leftName rightName modulus window endpointLedger readback provenance namecert endpoint =>
      change
        some
          (CauchyTailComparisonUp.mk
            (cauchyTailComparisonDecodeBHist (cauchyTailComparisonEncodeBHist leftName))
            (cauchyTailComparisonDecodeBHist (cauchyTailComparisonEncodeBHist rightName))
            (cauchyTailComparisonDecodeBHist (cauchyTailComparisonEncodeBHist modulus))
            (cauchyTailComparisonDecodeBHist (cauchyTailComparisonEncodeBHist window))
            (cauchyTailComparisonDecodeBHist
              (cauchyTailComparisonEncodeBHist endpointLedger))
            (cauchyTailComparisonDecodeBHist (cauchyTailComparisonEncodeBHist readback))
            (cauchyTailComparisonDecodeBHist (cauchyTailComparisonEncodeBHist provenance))
            (cauchyTailComparisonDecodeBHist (cauchyTailComparisonEncodeBHist namecert))
            (cauchyTailComparisonDecodeBHist (cauchyTailComparisonEncodeBHist endpoint))) =
          some
            (CauchyTailComparisonUp.mk leftName rightName modulus window endpointLedger readback
              provenance namecert endpoint)
      rw [cauchyTailComparisonDecode_encode_bhist leftName,
        cauchyTailComparisonDecode_encode_bhist rightName,
        cauchyTailComparisonDecode_encode_bhist modulus,
        cauchyTailComparisonDecode_encode_bhist window,
        cauchyTailComparisonDecode_encode_bhist endpointLedger,
        cauchyTailComparisonDecode_encode_bhist readback,
        cauchyTailComparisonDecode_encode_bhist provenance,
        cauchyTailComparisonDecode_encode_bhist namecert,
        cauchyTailComparisonDecode_encode_bhist endpoint]

private theorem cauchyTailComparisonToEventFlow_injective
    {x y : CauchyTailComparisonUp} :
    cauchyTailComparisonToEventFlow x = cauchyTailComparisonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyTailComparisonFromEventFlow (cauchyTailComparisonToEventFlow x) =
        cauchyTailComparisonFromEventFlow (cauchyTailComparisonToEventFlow y) :=
    congrArg cauchyTailComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyTailComparison_round_trip x).symm
      (Eq.trans hread (cauchyTailComparison_round_trip y)))

instance cauchyTailComparisonBHistCarrier : BHistCarrier CauchyTailComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyTailComparisonToEventFlow
  fromEventFlow := cauchyTailComparisonFromEventFlow

instance cauchyTailComparisonChapterTasteGate :
    ChapterTasteGate CauchyTailComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyTailComparisonFromEventFlow (cauchyTailComparisonToEventFlow x) = some x
    exact cauchyTailComparison_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyTailComparisonToEventFlow_injective heq)

theorem CauchyTailComparisonTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyTailComparisonDecodeBHist (cauchyTailComparisonEncodeBHist h) = h) ∧
      (∀ x : CauchyTailComparisonUp,
        cauchyTailComparisonFromEventFlow
          (cauchyTailComparisonToEventFlow x) = some x) ∧
        (∀ x y : CauchyTailComparisonUp,
          cauchyTailComparisonToEventFlow x = cauchyTailComparisonToEventFlow y → x = y) ∧
          cauchyTailComparisonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cauchyTailComparisonDecode_encode_bhist
  · constructor
    · exact cauchyTailComparison_round_trip
    · constructor
      · intro x y heq
        exact cauchyTailComparisonToEventFlow_injective heq
      · rfl

end BEDC.Derived.CauchyTailComparisonUp
