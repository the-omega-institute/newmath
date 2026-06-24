import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformCauchyModulusExtractorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformCauchyModulusExtractorUp : Type where
  | mk (uniformSource schedule modulus window dyadicLedger readback realSeal transport replay
      provenance nameCert : BHist) : UniformCauchyModulusExtractorUp
  deriving DecidableEq

def uniformCauchyModulusExtractorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformCauchyModulusExtractorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformCauchyModulusExtractorEncodeBHist h

def uniformCauchyModulusExtractorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformCauchyModulusExtractorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformCauchyModulusExtractorDecodeBHist tail)

private theorem uniformCauchyModulusExtractorDecode_encode_bhist :
    ∀ h : BHist,
      uniformCauchyModulusExtractorDecodeBHist
        (uniformCauchyModulusExtractorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformCauchyModulusExtractorToEventFlow :
    UniformCauchyModulusExtractorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | UniformCauchyModulusExtractorUp.mk uniformSource schedule modulus window dyadicLedger
      readback realSeal transport replay provenance nameCert =>
      [[BMark.b0],
        uniformCauchyModulusExtractorEncodeBHist uniformSource,
        [BMark.b1, BMark.b0],
        uniformCauchyModulusExtractorEncodeBHist schedule,
        [BMark.b1, BMark.b1, BMark.b0],
        uniformCauchyModulusExtractorEncodeBHist modulus,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        uniformCauchyModulusExtractorEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        uniformCauchyModulusExtractorEncodeBHist dyadicLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        uniformCauchyModulusExtractorEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        uniformCauchyModulusExtractorEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        uniformCauchyModulusExtractorEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        uniformCauchyModulusExtractorEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        uniformCauchyModulusExtractorEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        uniformCauchyModulusExtractorEncodeBHist nameCert]

def uniformCauchyModulusExtractorFromEventFlow :
    EventFlow → Option UniformCauchyModulusExtractorUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | uniformSource :: rest1 =>
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
                                      | dyadicLedger :: rest9 =>
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
                                                      | realSeal :: rest13 =>
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
                                                                      | replay :: rest17 =>
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
                                                                                                (UniformCauchyModulusExtractorUp.mk
                                                                                                  (uniformCauchyModulusExtractorDecodeBHist
                                                                                                    uniformSource)
                                                                                                  (uniformCauchyModulusExtractorDecodeBHist
                                                                                                    schedule)
                                                                                                  (uniformCauchyModulusExtractorDecodeBHist
                                                                                                    modulus)
                                                                                                  (uniformCauchyModulusExtractorDecodeBHist
                                                                                                    window)
                                                                                                  (uniformCauchyModulusExtractorDecodeBHist
                                                                                                    dyadicLedger)
                                                                                                  (uniformCauchyModulusExtractorDecodeBHist
                                                                                                    readback)
                                                                                                  (uniformCauchyModulusExtractorDecodeBHist
                                                                                                    realSeal)
                                                                                                  (uniformCauchyModulusExtractorDecodeBHist
                                                                                                    transport)
                                                                                                  (uniformCauchyModulusExtractorDecodeBHist
                                                                                                    replay)
                                                                                                  (uniformCauchyModulusExtractorDecodeBHist
                                                                                                    provenance)
                                                                                                  (uniformCauchyModulusExtractorDecodeBHist
                                                                                                    nameCert))
                                                                                          | _ :: _ => none

private theorem uniformCauchyModulusExtractor_round_trip :
    ∀ x : UniformCauchyModulusExtractorUp,
      uniformCauchyModulusExtractorFromEventFlow
        (uniformCauchyModulusExtractorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk uniformSource schedule modulus window dyadicLedger readback realSeal transport replay
      provenance nameCert =>
      change
        some (UniformCauchyModulusExtractorUp.mk
          (uniformCauchyModulusExtractorDecodeBHist
            (uniformCauchyModulusExtractorEncodeBHist uniformSource))
          (uniformCauchyModulusExtractorDecodeBHist
            (uniformCauchyModulusExtractorEncodeBHist schedule))
          (uniformCauchyModulusExtractorDecodeBHist
            (uniformCauchyModulusExtractorEncodeBHist modulus))
          (uniformCauchyModulusExtractorDecodeBHist
            (uniformCauchyModulusExtractorEncodeBHist window))
          (uniformCauchyModulusExtractorDecodeBHist
            (uniformCauchyModulusExtractorEncodeBHist dyadicLedger))
          (uniformCauchyModulusExtractorDecodeBHist
            (uniformCauchyModulusExtractorEncodeBHist readback))
          (uniformCauchyModulusExtractorDecodeBHist
            (uniformCauchyModulusExtractorEncodeBHist realSeal))
          (uniformCauchyModulusExtractorDecodeBHist
            (uniformCauchyModulusExtractorEncodeBHist transport))
          (uniformCauchyModulusExtractorDecodeBHist
            (uniformCauchyModulusExtractorEncodeBHist replay))
          (uniformCauchyModulusExtractorDecodeBHist
            (uniformCauchyModulusExtractorEncodeBHist provenance))
          (uniformCauchyModulusExtractorDecodeBHist
            (uniformCauchyModulusExtractorEncodeBHist nameCert))) =
          some (UniformCauchyModulusExtractorUp.mk uniformSource schedule modulus window
            dyadicLedger readback realSeal transport replay provenance nameCert)
      rw [uniformCauchyModulusExtractorDecode_encode_bhist uniformSource,
        uniformCauchyModulusExtractorDecode_encode_bhist schedule,
        uniformCauchyModulusExtractorDecode_encode_bhist modulus,
        uniformCauchyModulusExtractorDecode_encode_bhist window,
        uniformCauchyModulusExtractorDecode_encode_bhist dyadicLedger,
        uniformCauchyModulusExtractorDecode_encode_bhist readback,
        uniformCauchyModulusExtractorDecode_encode_bhist realSeal,
        uniformCauchyModulusExtractorDecode_encode_bhist transport,
        uniformCauchyModulusExtractorDecode_encode_bhist replay,
        uniformCauchyModulusExtractorDecode_encode_bhist provenance,
        uniformCauchyModulusExtractorDecode_encode_bhist nameCert]

private theorem uniformCauchyModulusExtractorToEventFlow_injective
    {x y : UniformCauchyModulusExtractorUp} :
    uniformCauchyModulusExtractorToEventFlow x =
      uniformCauchyModulusExtractorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformCauchyModulusExtractorFromEventFlow
          (uniformCauchyModulusExtractorToEventFlow x) =
        uniformCauchyModulusExtractorFromEventFlow
          (uniformCauchyModulusExtractorToEventFlow y) :=
    congrArg uniformCauchyModulusExtractorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (uniformCauchyModulusExtractor_round_trip x).symm
      (Eq.trans hread (uniformCauchyModulusExtractor_round_trip y)))

instance uniformCauchyModulusExtractorBHistCarrier :
    BHistCarrier UniformCauchyModulusExtractorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformCauchyModulusExtractorToEventFlow
  fromEventFlow := uniformCauchyModulusExtractorFromEventFlow

instance uniformCauchyModulusExtractorChapterTasteGate :
    ChapterTasteGate UniformCauchyModulusExtractorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformCauchyModulusExtractorFromEventFlow
        (uniformCauchyModulusExtractorToEventFlow x) = some x
    exact uniformCauchyModulusExtractor_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformCauchyModulusExtractorToEventFlow_injective heq)

theorem UniformCauchyModulusExtractorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      uniformCauchyModulusExtractorDecodeBHist
        (uniformCauchyModulusExtractorEncodeBHist h) = h) ∧
      (∀ x : UniformCauchyModulusExtractorUp,
        uniformCauchyModulusExtractorFromEventFlow
          (uniformCauchyModulusExtractorToEventFlow x) = some x) ∧
        (∀ x y : UniformCauchyModulusExtractorUp,
          uniformCauchyModulusExtractorToEventFlow x =
            uniformCauchyModulusExtractorToEventFlow y → x = y) ∧
          uniformCauchyModulusExtractorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact uniformCauchyModulusExtractorDecode_encode_bhist
  · constructor
    · exact uniformCauchyModulusExtractor_round_trip
    · constructor
      · intro x y heq
        exact uniformCauchyModulusExtractorToEventFlow_injective heq
      · rfl

end BEDC.Derived.UniformCauchyModulusExtractorUp
