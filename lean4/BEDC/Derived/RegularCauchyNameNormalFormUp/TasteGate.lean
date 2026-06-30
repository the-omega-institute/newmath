import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyNameNormalFormUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyNameNormalFormUp : Type where
  | mk (dyadic stream readback modulus realSeal bishopSeal transport route provenance name :
      BHist) : RegularCauchyNameNormalFormUp
  deriving DecidableEq

def regularCauchyNameNormalFormEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyNameNormalFormEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyNameNormalFormEncodeBHist h

def regularCauchyNameNormalFormDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyNameNormalFormDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyNameNormalFormDecodeBHist tail)

private theorem regularCauchyNameNormalFormDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchyNameNormalFormDecodeBHist
        (regularCauchyNameNormalFormEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyNameNormalFormToEventFlow :
    RegularCauchyNameNormalFormUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyNameNormalFormUp.mk dyadic stream readback modulus realSeal
      bishopSeal transport route provenance name =>
      [[BMark.b0],
        regularCauchyNameNormalFormEncodeBHist dyadic,
        [BMark.b1, BMark.b0],
        regularCauchyNameNormalFormEncodeBHist stream,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyNameNormalFormEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyNameNormalFormEncodeBHist modulus,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyNameNormalFormEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyNameNormalFormEncodeBHist bishopSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyNameNormalFormEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyNameNormalFormEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyNameNormalFormEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchyNameNormalFormEncodeBHist name]

def regularCauchyNameNormalFormFromEventFlow :
    EventFlow → Option RegularCauchyNameNormalFormUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | dyadic :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | stream :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | readback :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | modulus :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | realSeal :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | bishopSeal :: rest11 =>
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
                                                                      | provenance :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | name :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (RegularCauchyNameNormalFormUp.mk
                                                                                          (regularCauchyNameNormalFormDecodeBHist
                                                                                            dyadic)
                                                                                          (regularCauchyNameNormalFormDecodeBHist
                                                                                            stream)
                                                                                          (regularCauchyNameNormalFormDecodeBHist
                                                                                            readback)
                                                                                          (regularCauchyNameNormalFormDecodeBHist
                                                                                            modulus)
                                                                                          (regularCauchyNameNormalFormDecodeBHist
                                                                                            realSeal)
                                                                                          (regularCauchyNameNormalFormDecodeBHist
                                                                                            bishopSeal)
                                                                                          (regularCauchyNameNormalFormDecodeBHist
                                                                                            transport)
                                                                                          (regularCauchyNameNormalFormDecodeBHist
                                                                                            route)
                                                                                          (regularCauchyNameNormalFormDecodeBHist
                                                                                            provenance)
                                                                                          (regularCauchyNameNormalFormDecodeBHist
                                                                                            name))
                                                                                  | _ :: _ => none

private theorem regularCauchyNameNormalForm_round_trip :
    ∀ x : RegularCauchyNameNormalFormUp,
      regularCauchyNameNormalFormFromEventFlow
        (regularCauchyNameNormalFormToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk dyadic stream readback modulus realSeal bishopSeal transport route provenance name =>
      change
        some
          (RegularCauchyNameNormalFormUp.mk
            (regularCauchyNameNormalFormDecodeBHist
              (regularCauchyNameNormalFormEncodeBHist dyadic))
            (regularCauchyNameNormalFormDecodeBHist
              (regularCauchyNameNormalFormEncodeBHist stream))
            (regularCauchyNameNormalFormDecodeBHist
              (regularCauchyNameNormalFormEncodeBHist readback))
            (regularCauchyNameNormalFormDecodeBHist
              (regularCauchyNameNormalFormEncodeBHist modulus))
            (regularCauchyNameNormalFormDecodeBHist
              (regularCauchyNameNormalFormEncodeBHist realSeal))
            (regularCauchyNameNormalFormDecodeBHist
              (regularCauchyNameNormalFormEncodeBHist bishopSeal))
            (regularCauchyNameNormalFormDecodeBHist
              (regularCauchyNameNormalFormEncodeBHist transport))
            (regularCauchyNameNormalFormDecodeBHist
              (regularCauchyNameNormalFormEncodeBHist route))
            (regularCauchyNameNormalFormDecodeBHist
              (regularCauchyNameNormalFormEncodeBHist provenance))
            (regularCauchyNameNormalFormDecodeBHist
              (regularCauchyNameNormalFormEncodeBHist name))) =
          some
            (RegularCauchyNameNormalFormUp.mk dyadic stream readback modulus realSeal
              bishopSeal transport route provenance name)
      rw [regularCauchyNameNormalFormDecode_encode_bhist dyadic,
        regularCauchyNameNormalFormDecode_encode_bhist stream,
        regularCauchyNameNormalFormDecode_encode_bhist readback,
        regularCauchyNameNormalFormDecode_encode_bhist modulus,
        regularCauchyNameNormalFormDecode_encode_bhist realSeal,
        regularCauchyNameNormalFormDecode_encode_bhist bishopSeal,
        regularCauchyNameNormalFormDecode_encode_bhist transport,
        regularCauchyNameNormalFormDecode_encode_bhist route,
        regularCauchyNameNormalFormDecode_encode_bhist provenance,
        regularCauchyNameNormalFormDecode_encode_bhist name]

private theorem regularCauchyNameNormalFormToEventFlow_injective
    {x y : RegularCauchyNameNormalFormUp} :
    regularCauchyNameNormalFormToEventFlow x =
        regularCauchyNameNormalFormToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyNameNormalFormFromEventFlow
          (regularCauchyNameNormalFormToEventFlow x) =
        regularCauchyNameNormalFormFromEventFlow
          (regularCauchyNameNormalFormToEventFlow y) :=
    congrArg regularCauchyNameNormalFormFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyNameNormalForm_round_trip x).symm
      (Eq.trans hread (regularCauchyNameNormalForm_round_trip y)))

instance regularCauchyNameNormalFormBHistCarrier :
    BHistCarrier RegularCauchyNameNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyNameNormalFormToEventFlow
  fromEventFlow := regularCauchyNameNormalFormFromEventFlow

instance regularCauchyNameNormalFormChapterTasteGate :
    ChapterTasteGate RegularCauchyNameNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyNameNormalFormFromEventFlow
        (regularCauchyNameNormalFormToEventFlow x) = some x
    exact regularCauchyNameNormalForm_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyNameNormalFormToEventFlow_injective heq)

theorem RegularCauchyNameNormalFormTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        regularCauchyNameNormalFormDecodeBHist
          (regularCauchyNameNormalFormEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyNameNormalFormUp,
        regularCauchyNameNormalFormFromEventFlow
          (regularCauchyNameNormalFormToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyNameNormalFormUp,
          regularCauchyNameNormalFormToEventFlow x =
              regularCauchyNameNormalFormToEventFlow y →
            x = y) ∧
          regularCauchyNameNormalFormEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyNameNormalFormDecode_encode_bhist
  · constructor
    · exact regularCauchyNameNormalForm_round_trip
    · constructor
      · intro x y heq
        exact regularCauchyNameNormalFormToEventFlow_injective heq
      · rfl

end BEDC.Derived.RegularCauchyNameNormalFormUp
