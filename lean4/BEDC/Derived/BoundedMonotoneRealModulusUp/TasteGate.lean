import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedMonotoneRealModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedMonotoneRealModulusUp : Type where
  | mk : (W T D S Q R H C P N : BHist) → BoundedMonotoneRealModulusUp
  deriving DecidableEq

def boundedMonotoneRealModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedMonotoneRealModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedMonotoneRealModulusEncodeBHist h

def boundedMonotoneRealModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedMonotoneRealModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedMonotoneRealModulusDecodeBHist tail)

private theorem boundedMonotoneRealModulusDecode_encode_bhist :
    ∀ h : BHist,
      boundedMonotoneRealModulusDecodeBHist
          (boundedMonotoneRealModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def boundedMonotoneRealModulusToEventFlow :
    BoundedMonotoneRealModulusUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BoundedMonotoneRealModulusUp.mk W T D S Q R H C P N =>
      [[BMark.b0],
        boundedMonotoneRealModulusEncodeBHist W,
        [BMark.b1, BMark.b0],
        boundedMonotoneRealModulusEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b0],
        boundedMonotoneRealModulusEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedMonotoneRealModulusEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedMonotoneRealModulusEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedMonotoneRealModulusEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedMonotoneRealModulusEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        boundedMonotoneRealModulusEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        boundedMonotoneRealModulusEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        boundedMonotoneRealModulusEncodeBHist N]

def boundedMonotoneRealModulusFromEventFlow :
    EventFlow → Option BoundedMonotoneRealModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: rest0 =>
      match rest0 with
      | [] => none
      | W :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | T :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | D :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | S :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | Q :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | R :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | H :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | C :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | P :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | N :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (BoundedMonotoneRealModulusUp.mk
                                                                                          (boundedMonotoneRealModulusDecodeBHist W)
                                                                                          (boundedMonotoneRealModulusDecodeBHist T)
                                                                                          (boundedMonotoneRealModulusDecodeBHist D)
                                                                                          (boundedMonotoneRealModulusDecodeBHist S)
                                                                                          (boundedMonotoneRealModulusDecodeBHist Q)
                                                                                          (boundedMonotoneRealModulusDecodeBHist R)
                                                                                          (boundedMonotoneRealModulusDecodeBHist H)
                                                                                          (boundedMonotoneRealModulusDecodeBHist C)
                                                                                          (boundedMonotoneRealModulusDecodeBHist P)
                                                                                          (boundedMonotoneRealModulusDecodeBHist N))
                                                                                  | _ :: _ => none

private theorem boundedMonotoneRealModulus_round_trip :
    ∀ x : BoundedMonotoneRealModulusUp,
      boundedMonotoneRealModulusFromEventFlow
          (boundedMonotoneRealModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W T D S Q R H C P N =>
      change
        some
          (BoundedMonotoneRealModulusUp.mk
            (boundedMonotoneRealModulusDecodeBHist
              (boundedMonotoneRealModulusEncodeBHist W))
            (boundedMonotoneRealModulusDecodeBHist
              (boundedMonotoneRealModulusEncodeBHist T))
            (boundedMonotoneRealModulusDecodeBHist
              (boundedMonotoneRealModulusEncodeBHist D))
            (boundedMonotoneRealModulusDecodeBHist
              (boundedMonotoneRealModulusEncodeBHist S))
            (boundedMonotoneRealModulusDecodeBHist
              (boundedMonotoneRealModulusEncodeBHist Q))
            (boundedMonotoneRealModulusDecodeBHist
              (boundedMonotoneRealModulusEncodeBHist R))
            (boundedMonotoneRealModulusDecodeBHist
              (boundedMonotoneRealModulusEncodeBHist H))
            (boundedMonotoneRealModulusDecodeBHist
              (boundedMonotoneRealModulusEncodeBHist C))
            (boundedMonotoneRealModulusDecodeBHist
              (boundedMonotoneRealModulusEncodeBHist P))
            (boundedMonotoneRealModulusDecodeBHist
              (boundedMonotoneRealModulusEncodeBHist N))) =
          some (BoundedMonotoneRealModulusUp.mk W T D S Q R H C P N)
      rw [boundedMonotoneRealModulusDecode_encode_bhist W,
        boundedMonotoneRealModulusDecode_encode_bhist T,
        boundedMonotoneRealModulusDecode_encode_bhist D,
        boundedMonotoneRealModulusDecode_encode_bhist S,
        boundedMonotoneRealModulusDecode_encode_bhist Q,
        boundedMonotoneRealModulusDecode_encode_bhist R,
        boundedMonotoneRealModulusDecode_encode_bhist H,
        boundedMonotoneRealModulusDecode_encode_bhist C,
        boundedMonotoneRealModulusDecode_encode_bhist P,
        boundedMonotoneRealModulusDecode_encode_bhist N]

private theorem boundedMonotoneRealModulusToEventFlow_injective
    {x y : BoundedMonotoneRealModulusUp} :
    boundedMonotoneRealModulusToEventFlow x =
        boundedMonotoneRealModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          boundedMonotoneRealModulusFromEventFlow
            (boundedMonotoneRealModulusToEventFlow x) :=
        (boundedMonotoneRealModulus_round_trip x).symm
      _ =
          boundedMonotoneRealModulusFromEventFlow
            (boundedMonotoneRealModulusToEventFlow y) :=
        congrArg boundedMonotoneRealModulusFromEventFlow hxy
      _ = some y := boundedMonotoneRealModulus_round_trip y
  exact Option.some.inj optionEq

instance boundedMonotoneRealModulusBHistCarrier :
    BHistCarrier BoundedMonotoneRealModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedMonotoneRealModulusToEventFlow
  fromEventFlow := boundedMonotoneRealModulusFromEventFlow

instance boundedMonotoneRealModulusChapterTasteGate :
    ChapterTasteGate BoundedMonotoneRealModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      boundedMonotoneRealModulusFromEventFlow
          (boundedMonotoneRealModulusToEventFlow x) = some x
    exact boundedMonotoneRealModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (boundedMonotoneRealModulusToEventFlow_injective heq)

theorem BoundedMonotoneRealModulusTasteGate_single_carrier_alignment
    (W T D S Q R H C P N : BHist) :
    boundedMonotoneRealModulusToEventFlow
        (BoundedMonotoneRealModulusUp.mk W T D S Q R H C P N) =
        [[BMark.b0],
          boundedMonotoneRealModulusEncodeBHist W,
          [BMark.b1, BMark.b0],
          boundedMonotoneRealModulusEncodeBHist T,
          [BMark.b1, BMark.b1, BMark.b0],
          boundedMonotoneRealModulusEncodeBHist D,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          boundedMonotoneRealModulusEncodeBHist S,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          boundedMonotoneRealModulusEncodeBHist Q,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          boundedMonotoneRealModulusEncodeBHist R,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          boundedMonotoneRealModulusEncodeBHist H,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          boundedMonotoneRealModulusEncodeBHist C,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          boundedMonotoneRealModulusEncodeBHist P,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b0],
          boundedMonotoneRealModulusEncodeBHist N] := by
  -- BEDC touchpoint anchor: BHist BMark
  rfl

end BEDC.Derived.BoundedMonotoneRealModulusUp
