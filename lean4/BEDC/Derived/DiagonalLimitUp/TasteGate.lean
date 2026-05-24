import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DiagonalLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DiagonalLimitUp : Type where
  | mk :
      (family modulus stream dyadic completion sealRow route provenance : BHist) →
      DiagonalLimitUp

def diagonalLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: diagonalLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: diagonalLimitEncodeBHist h

def diagonalLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (diagonalLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (diagonalLimitDecodeBHist tail)

private theorem diagonalLimitDecode_encode_bhist :
    ∀ h : BHist, diagonalLimitDecodeBHist (diagonalLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def diagonalLimitToEventFlow : DiagonalLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DiagonalLimitUp.mk family modulus stream dyadic completion sealRow route provenance =>
      [[BMark.b0],
        diagonalLimitEncodeBHist family,
        [BMark.b1, BMark.b0],
        diagonalLimitEncodeBHist modulus,
        [BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitEncodeBHist stream,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitEncodeBHist dyadic,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitEncodeBHist completion,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitEncodeBHist sealRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        diagonalLimitEncodeBHist provenance]

def diagonalLimitFromEventFlow : EventFlow → Option DiagonalLimitUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | family :: rest1 =>
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
                      | stream :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | dyadic :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | completion :: rest9 =>
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
                                                      | route :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (DiagonalLimitUp.mk
                                                                          (diagonalLimitDecodeBHist family)
                                                                          (diagonalLimitDecodeBHist modulus)
                                                                          (diagonalLimitDecodeBHist stream)
                                                                          (diagonalLimitDecodeBHist dyadic)
                                                                          (diagonalLimitDecodeBHist completion)
                                                                          (diagonalLimitDecodeBHist sealRow)
                                                                          (diagonalLimitDecodeBHist route)
                                                                          (diagonalLimitDecodeBHist provenance))
                                                                  | _ :: _ => none

private theorem diagonalLimit_round_trip :
    ∀ x : DiagonalLimitUp,
      diagonalLimitFromEventFlow (diagonalLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk family modulus stream dyadic completion sealRow route provenance =>
      change
        some
          (DiagonalLimitUp.mk
            (diagonalLimitDecodeBHist (diagonalLimitEncodeBHist family))
            (diagonalLimitDecodeBHist (diagonalLimitEncodeBHist modulus))
            (diagonalLimitDecodeBHist (diagonalLimitEncodeBHist stream))
            (diagonalLimitDecodeBHist (diagonalLimitEncodeBHist dyadic))
            (diagonalLimitDecodeBHist (diagonalLimitEncodeBHist completion))
            (diagonalLimitDecodeBHist (diagonalLimitEncodeBHist sealRow))
            (diagonalLimitDecodeBHist (diagonalLimitEncodeBHist route))
            (diagonalLimitDecodeBHist (diagonalLimitEncodeBHist provenance))) =
          some
            (DiagonalLimitUp.mk family modulus stream dyadic completion sealRow route provenance)
      rw [diagonalLimitDecode_encode_bhist family,
        diagonalLimitDecode_encode_bhist modulus,
        diagonalLimitDecode_encode_bhist stream,
        diagonalLimitDecode_encode_bhist dyadic,
        diagonalLimitDecode_encode_bhist completion,
        diagonalLimitDecode_encode_bhist sealRow,
        diagonalLimitDecode_encode_bhist route,
        diagonalLimitDecode_encode_bhist provenance]

private theorem diagonalLimitToEventFlow_injective {x y : DiagonalLimitUp} :
    diagonalLimitToEventFlow x = diagonalLimitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      diagonalLimitFromEventFlow (diagonalLimitToEventFlow x) =
        diagonalLimitFromEventFlow (diagonalLimitToEventFlow y) :=
    congrArg diagonalLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (diagonalLimit_round_trip x).symm
      (Eq.trans hread (diagonalLimit_round_trip y)))

instance diagonalLimitBHistCarrier : BHistCarrier DiagonalLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := diagonalLimitToEventFlow
  fromEventFlow := diagonalLimitFromEventFlow

instance diagonalLimitChapterTasteGate : ChapterTasteGate DiagonalLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change diagonalLimitFromEventFlow (diagonalLimitToEventFlow x) = some x
    exact diagonalLimit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (diagonalLimitToEventFlow_injective heq)

theorem DiagonalLimitTasteGate_single_carrier_alignment :
    (∀ h : BHist, diagonalLimitDecodeBHist (diagonalLimitEncodeBHist h) = h) ∧
      (∀ x : DiagonalLimitUp,
        diagonalLimitFromEventFlow (diagonalLimitToEventFlow x) = some x) ∧
        (∀ x y : DiagonalLimitUp,
          diagonalLimitToEventFlow x = diagonalLimitToEventFlow y → x = y) ∧
          diagonalLimitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact diagonalLimitDecode_encode_bhist
  · constructor
    · exact diagonalLimit_round_trip
    · constructor
      · intro x y heq
        exact diagonalLimitToEventFlow_injective heq
      · rfl

end BEDC.Derived.DiagonalLimitUp
