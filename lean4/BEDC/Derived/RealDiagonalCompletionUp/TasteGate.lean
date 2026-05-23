import BEDC.Derived.RealDiagonalCompletionUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealDiagonalCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealDiagonalCompletionUp : Type where
  | mk :
      (inputFamily modulus diagonal schedule readback sealRow provenance name : BHist) →
        RealDiagonalCompletionUp
  deriving DecidableEq

def realDiagonalCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realDiagonalCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realDiagonalCompletionEncodeBHist h

def realDiagonalCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realDiagonalCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realDiagonalCompletionDecodeBHist tail)

private theorem realDiagonalCompletionDecode_encode_bhist :
    ∀ h : BHist,
      realDiagonalCompletionDecodeBHist (realDiagonalCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realDiagonalCompletionToEventFlow : RealDiagonalCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealDiagonalCompletionUp.mk inputFamily modulus diagonal schedule readback sealRow provenance
      name =>
      [[BMark.b0],
        realDiagonalCompletionEncodeBHist inputFamily,
        [BMark.b1, BMark.b0],
        realDiagonalCompletionEncodeBHist modulus,
        [BMark.b1, BMark.b1, BMark.b0],
        realDiagonalCompletionEncodeBHist diagonal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realDiagonalCompletionEncodeBHist schedule,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realDiagonalCompletionEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realDiagonalCompletionEncodeBHist sealRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realDiagonalCompletionEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realDiagonalCompletionEncodeBHist name]

def realDiagonalCompletionFromEventFlow : EventFlow → Option RealDiagonalCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | inputFamily :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | modulus :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | diagonal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | schedule :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | readback :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | sealRow :: rest11 =>
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
                                                                        (RealDiagonalCompletionUp.mk
                                                                          (realDiagonalCompletionDecodeBHist
                                                                            inputFamily)
                                                                          (realDiagonalCompletionDecodeBHist
                                                                            modulus)
                                                                          (realDiagonalCompletionDecodeBHist
                                                                            diagonal)
                                                                          (realDiagonalCompletionDecodeBHist
                                                                            schedule)
                                                                          (realDiagonalCompletionDecodeBHist
                                                                            readback)
                                                                          (realDiagonalCompletionDecodeBHist
                                                                            sealRow)
                                                                          (realDiagonalCompletionDecodeBHist
                                                                            provenance)
                                                                          (realDiagonalCompletionDecodeBHist
                                                                            name))
                                                                  | _ :: _ => none

private theorem realDiagonalCompletion_round_trip :
    ∀ x : RealDiagonalCompletionUp,
      realDiagonalCompletionFromEventFlow (realDiagonalCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk inputFamily modulus diagonal schedule readback sealRow provenance name =>
      change
        some
          (RealDiagonalCompletionUp.mk
            (realDiagonalCompletionDecodeBHist
              (realDiagonalCompletionEncodeBHist inputFamily))
            (realDiagonalCompletionDecodeBHist (realDiagonalCompletionEncodeBHist modulus))
            (realDiagonalCompletionDecodeBHist (realDiagonalCompletionEncodeBHist diagonal))
            (realDiagonalCompletionDecodeBHist (realDiagonalCompletionEncodeBHist schedule))
            (realDiagonalCompletionDecodeBHist (realDiagonalCompletionEncodeBHist readback))
            (realDiagonalCompletionDecodeBHist (realDiagonalCompletionEncodeBHist sealRow))
            (realDiagonalCompletionDecodeBHist
              (realDiagonalCompletionEncodeBHist provenance))
            (realDiagonalCompletionDecodeBHist (realDiagonalCompletionEncodeBHist name))) =
          some
            (RealDiagonalCompletionUp.mk inputFamily modulus diagonal schedule readback sealRow
              provenance name)
      rw [realDiagonalCompletionDecode_encode_bhist inputFamily,
        realDiagonalCompletionDecode_encode_bhist modulus,
        realDiagonalCompletionDecode_encode_bhist diagonal,
        realDiagonalCompletionDecode_encode_bhist schedule,
        realDiagonalCompletionDecode_encode_bhist readback,
        realDiagonalCompletionDecode_encode_bhist sealRow,
        realDiagonalCompletionDecode_encode_bhist provenance,
        realDiagonalCompletionDecode_encode_bhist name]

private theorem realDiagonalCompletionToEventFlow_injective
    {x y : RealDiagonalCompletionUp} :
    realDiagonalCompletionToEventFlow x = realDiagonalCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realDiagonalCompletionFromEventFlow (realDiagonalCompletionToEventFlow x) =
        realDiagonalCompletionFromEventFlow (realDiagonalCompletionToEventFlow y) :=
    congrArg realDiagonalCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realDiagonalCompletion_round_trip x).symm
      (Eq.trans hread (realDiagonalCompletion_round_trip y)))

instance realDiagonalCompletionBHistCarrier : BHistCarrier RealDiagonalCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realDiagonalCompletionToEventFlow
  fromEventFlow := realDiagonalCompletionFromEventFlow

instance realDiagonalCompletionChapterTasteGate :
    ChapterTasteGate RealDiagonalCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realDiagonalCompletionFromEventFlow (realDiagonalCompletionToEventFlow x) = some x
    exact realDiagonalCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realDiagonalCompletionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealDiagonalCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realDiagonalCompletionChapterTasteGate

theorem RealDiagonalCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realDiagonalCompletionDecodeBHist (realDiagonalCompletionEncodeBHist h) = h) ∧
      (∀ x : RealDiagonalCompletionUp,
        realDiagonalCompletionFromEventFlow (realDiagonalCompletionToEventFlow x) = some x) ∧
        (∀ x y : RealDiagonalCompletionUp,
          realDiagonalCompletionToEventFlow x = realDiagonalCompletionToEventFlow y → x = y) ∧
          realDiagonalCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact realDiagonalCompletionDecode_encode_bhist
  · constructor
    · exact realDiagonalCompletion_round_trip
    · constructor
      · intro x y heq
        exact realDiagonalCompletionToEventFlow_injective heq
      · rfl

end BEDC.Derived.RealDiagonalCompletionUp
