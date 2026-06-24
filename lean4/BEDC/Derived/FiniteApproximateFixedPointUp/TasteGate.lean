import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteApproximateFixedPointUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteApproximateFixedPointUp : Type where
  | mk (compact map finiteNet ball displacement realSeal handoff transport replay provenance
      nameCert : BHist) : FiniteApproximateFixedPointUp
  deriving DecidableEq

def finiteApproximateFixedPointEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteApproximateFixedPointEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteApproximateFixedPointEncodeBHist h

def finiteApproximateFixedPointDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteApproximateFixedPointDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteApproximateFixedPointDecodeBHist tail)

private theorem finiteApproximateFixedPointDecode_encode_bhist :
    ∀ h : BHist, finiteApproximateFixedPointDecodeBHist
      (finiteApproximateFixedPointEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteApproximateFixedPointToEventFlow :
    FiniteApproximateFixedPointUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteApproximateFixedPointUp.mk compact map finiteNet ball displacement realSeal handoff
      transport replay provenance nameCert =>
      [[BMark.b0],
        finiteApproximateFixedPointEncodeBHist compact,
        [BMark.b1, BMark.b0],
        finiteApproximateFixedPointEncodeBHist map,
        [BMark.b1, BMark.b1, BMark.b0],
        finiteApproximateFixedPointEncodeBHist finiteNet,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteApproximateFixedPointEncodeBHist ball,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteApproximateFixedPointEncodeBHist displacement,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteApproximateFixedPointEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteApproximateFixedPointEncodeBHist handoff,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        finiteApproximateFixedPointEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        finiteApproximateFixedPointEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        finiteApproximateFixedPointEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteApproximateFixedPointEncodeBHist nameCert]

def finiteApproximateFixedPointFromEventFlow :
    EventFlow → Option FiniteApproximateFixedPointUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | compact :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | map :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | finiteNet :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | ball :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | displacement :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | realSeal :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | handoff :: rest13 =>
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
                                                                                                (FiniteApproximateFixedPointUp.mk
                                                                                                  (finiteApproximateFixedPointDecodeBHist
                                                                                                    compact)
                                                                                                  (finiteApproximateFixedPointDecodeBHist
                                                                                                    map)
                                                                                                  (finiteApproximateFixedPointDecodeBHist
                                                                                                    finiteNet)
                                                                                                  (finiteApproximateFixedPointDecodeBHist
                                                                                                    ball)
                                                                                                  (finiteApproximateFixedPointDecodeBHist
                                                                                                    displacement)
                                                                                                  (finiteApproximateFixedPointDecodeBHist
                                                                                                    realSeal)
                                                                                                  (finiteApproximateFixedPointDecodeBHist
                                                                                                    handoff)
                                                                                                  (finiteApproximateFixedPointDecodeBHist
                                                                                                    transport)
                                                                                                  (finiteApproximateFixedPointDecodeBHist
                                                                                                    replay)
                                                                                                  (finiteApproximateFixedPointDecodeBHist
                                                                                                    provenance)
                                                                                                  (finiteApproximateFixedPointDecodeBHist
                                                                                                    nameCert))
                                                                                          | _ :: _ => none
private theorem finiteApproximateFixedPoint_round_trip :
    ∀ x : FiniteApproximateFixedPointUp,
      finiteApproximateFixedPointFromEventFlow
        (finiteApproximateFixedPointToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk compact map finiteNet ball displacement realSeal handoff transport replay provenance
      nameCert =>
      change
        some (FiniteApproximateFixedPointUp.mk
          (finiteApproximateFixedPointDecodeBHist
            (finiteApproximateFixedPointEncodeBHist compact))
          (finiteApproximateFixedPointDecodeBHist
            (finiteApproximateFixedPointEncodeBHist map))
          (finiteApproximateFixedPointDecodeBHist
            (finiteApproximateFixedPointEncodeBHist finiteNet))
          (finiteApproximateFixedPointDecodeBHist
            (finiteApproximateFixedPointEncodeBHist ball))
          (finiteApproximateFixedPointDecodeBHist
            (finiteApproximateFixedPointEncodeBHist displacement))
          (finiteApproximateFixedPointDecodeBHist
            (finiteApproximateFixedPointEncodeBHist realSeal))
          (finiteApproximateFixedPointDecodeBHist
            (finiteApproximateFixedPointEncodeBHist handoff))
          (finiteApproximateFixedPointDecodeBHist
            (finiteApproximateFixedPointEncodeBHist transport))
          (finiteApproximateFixedPointDecodeBHist
            (finiteApproximateFixedPointEncodeBHist replay))
          (finiteApproximateFixedPointDecodeBHist
            (finiteApproximateFixedPointEncodeBHist provenance))
          (finiteApproximateFixedPointDecodeBHist
            (finiteApproximateFixedPointEncodeBHist nameCert))) =
          some (FiniteApproximateFixedPointUp.mk compact map finiteNet ball displacement
            realSeal handoff transport replay provenance nameCert)
      rw [finiteApproximateFixedPointDecode_encode_bhist compact,
        finiteApproximateFixedPointDecode_encode_bhist map,
        finiteApproximateFixedPointDecode_encode_bhist finiteNet,
        finiteApproximateFixedPointDecode_encode_bhist ball,
        finiteApproximateFixedPointDecode_encode_bhist displacement,
        finiteApproximateFixedPointDecode_encode_bhist realSeal,
        finiteApproximateFixedPointDecode_encode_bhist handoff,
        finiteApproximateFixedPointDecode_encode_bhist transport,
        finiteApproximateFixedPointDecode_encode_bhist replay,
        finiteApproximateFixedPointDecode_encode_bhist provenance,
        finiteApproximateFixedPointDecode_encode_bhist nameCert]

private theorem finiteApproximateFixedPointToEventFlow_injective
    {x y : FiniteApproximateFixedPointUp} :
    finiteApproximateFixedPointToEventFlow x =
        finiteApproximateFixedPointToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteApproximateFixedPointFromEventFlow
          (finiteApproximateFixedPointToEventFlow x) =
        finiteApproximateFixedPointFromEventFlow
          (finiteApproximateFixedPointToEventFlow y) :=
    congrArg finiteApproximateFixedPointFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteApproximateFixedPoint_round_trip x).symm
      (Eq.trans hread (finiteApproximateFixedPoint_round_trip y)))

instance finiteApproximateFixedPointBHistCarrier :
    BHistCarrier FiniteApproximateFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteApproximateFixedPointToEventFlow
  fromEventFlow := finiteApproximateFixedPointFromEventFlow

instance finiteApproximateFixedPointChapterTasteGate :
    ChapterTasteGate FiniteApproximateFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteApproximateFixedPointFromEventFlow
        (finiteApproximateFixedPointToEventFlow x) = some x
    exact finiteApproximateFixedPoint_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteApproximateFixedPointToEventFlow_injective heq)

theorem FiniteApproximateFixedPointTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteApproximateFixedPointDecodeBHist
      (finiteApproximateFixedPointEncodeBHist h) = h) ∧
      (∀ x : FiniteApproximateFixedPointUp,
        finiteApproximateFixedPointFromEventFlow
          (finiteApproximateFixedPointToEventFlow x) = some x) ∧
        (∀ x y : FiniteApproximateFixedPointUp,
          finiteApproximateFixedPointToEventFlow x =
              finiteApproximateFixedPointToEventFlow y →
            x = y) ∧
          finiteApproximateFixedPointEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact finiteApproximateFixedPointDecode_encode_bhist
  · constructor
    · exact finiteApproximateFixedPoint_round_trip
    · constructor
      · intro x y heq
        exact finiteApproximateFixedPointToEventFlow_injective heq
      · rfl

end BEDC.Derived.FiniteApproximateFixedPointUp
