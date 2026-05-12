import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealScheduleFusionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealScheduleFusionUp : Type where
  | mk :
      (schedule window readback sealRow transport route provenance name : BHist) →
        RealScheduleFusionUp
  deriving DecidableEq

def realScheduleFusionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realScheduleFusionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realScheduleFusionEncodeBHist h

def realScheduleFusionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realScheduleFusionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realScheduleFusionDecodeBHist tail)

private theorem realScheduleFusionDecode_encode_bhist :
    ∀ h : BHist, realScheduleFusionDecodeBHist (realScheduleFusionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realScheduleFusionToEventFlow : RealScheduleFusionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealScheduleFusionUp.mk schedule window readback sealRow transport route provenance name =>
      [[BMark.b0],
        realScheduleFusionEncodeBHist schedule,
        [BMark.b1, BMark.b0],
        realScheduleFusionEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b0],
        realScheduleFusionEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realScheduleFusionEncodeBHist sealRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realScheduleFusionEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realScheduleFusionEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realScheduleFusionEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realScheduleFusionEncodeBHist name]

def realScheduleFusionFromEventFlow : EventFlow → Option RealScheduleFusionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | schedule :: rest1 =>
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
                      | readback :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | sealRow :: rest7 =>
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
                                              | route :: rest11 =>
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
                                                                        (RealScheduleFusionUp.mk
                                                                          (realScheduleFusionDecodeBHist
                                                                            schedule)
                                                                          (realScheduleFusionDecodeBHist
                                                                            window)
                                                                          (realScheduleFusionDecodeBHist
                                                                            readback)
                                                                          (realScheduleFusionDecodeBHist
                                                                            sealRow)
                                                                          (realScheduleFusionDecodeBHist
                                                                            transport)
                                                                          (realScheduleFusionDecodeBHist
                                                                            route)
                                                                          (realScheduleFusionDecodeBHist
                                                                            provenance)
                                                                          (realScheduleFusionDecodeBHist
                                                                            name))
                                                                  | _ :: _ => none

private theorem realScheduleFusion_round_trip :
    ∀ x : RealScheduleFusionUp,
      realScheduleFusionFromEventFlow (realScheduleFusionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk schedule window readback sealRow transport route provenance name =>
      change
        some
          (RealScheduleFusionUp.mk
            (realScheduleFusionDecodeBHist (realScheduleFusionEncodeBHist schedule))
            (realScheduleFusionDecodeBHist (realScheduleFusionEncodeBHist window))
            (realScheduleFusionDecodeBHist (realScheduleFusionEncodeBHist readback))
            (realScheduleFusionDecodeBHist (realScheduleFusionEncodeBHist sealRow))
            (realScheduleFusionDecodeBHist (realScheduleFusionEncodeBHist transport))
            (realScheduleFusionDecodeBHist (realScheduleFusionEncodeBHist route))
            (realScheduleFusionDecodeBHist (realScheduleFusionEncodeBHist provenance))
            (realScheduleFusionDecodeBHist (realScheduleFusionEncodeBHist name))) =
          some
            (RealScheduleFusionUp.mk schedule window readback sealRow transport route provenance
              name)
      rw [realScheduleFusionDecode_encode_bhist schedule,
        realScheduleFusionDecode_encode_bhist window,
        realScheduleFusionDecode_encode_bhist readback,
        realScheduleFusionDecode_encode_bhist sealRow,
        realScheduleFusionDecode_encode_bhist transport,
        realScheduleFusionDecode_encode_bhist route,
        realScheduleFusionDecode_encode_bhist provenance,
        realScheduleFusionDecode_encode_bhist name]

private theorem realScheduleFusionToEventFlow_injective {x y : RealScheduleFusionUp} :
    realScheduleFusionToEventFlow x = realScheduleFusionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realScheduleFusionFromEventFlow (realScheduleFusionToEventFlow x) =
        realScheduleFusionFromEventFlow (realScheduleFusionToEventFlow y) :=
    congrArg realScheduleFusionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realScheduleFusion_round_trip x).symm
      (Eq.trans hread (realScheduleFusion_round_trip y)))

instance realScheduleFusionBHistCarrier : BHistCarrier RealScheduleFusionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realScheduleFusionToEventFlow
  fromEventFlow := realScheduleFusionFromEventFlow

instance realScheduleFusionChapterTasteGate : ChapterTasteGate RealScheduleFusionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realScheduleFusionFromEventFlow (realScheduleFusionToEventFlow x) = some x
    exact realScheduleFusion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realScheduleFusionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealScheduleFusionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realScheduleFusionChapterTasteGate

theorem RealScheduleFusionTasteGate_single_carrier_alignment :
    (∀ h : BHist, realScheduleFusionDecodeBHist (realScheduleFusionEncodeBHist h) = h) ∧
      (∀ x : RealScheduleFusionUp,
        realScheduleFusionFromEventFlow (realScheduleFusionToEventFlow x) = some x) ∧
        (∀ x y : RealScheduleFusionUp,
          realScheduleFusionToEventFlow x = realScheduleFusionToEventFlow y → x = y) ∧
          realScheduleFusionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact realScheduleFusionDecode_encode_bhist
  · constructor
    · exact realScheduleFusion_round_trip
    · constructor
      · intro x y heq
        exact realScheduleFusionToEventFlow_injective heq
      · rfl

end BEDC.Derived.RealScheduleFusionUp
