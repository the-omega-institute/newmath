import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCompletionTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCompletionTheoremUp : Type where
  | mk
      (modulus stream readback realSeal universalHandoff transport replay provenance name : BHist) :
      BishopCompletionTheoremUp
  deriving DecidableEq

def bishopCompletionTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCompletionTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCompletionTheoremEncodeBHist h

def bishopCompletionTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCompletionTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCompletionTheoremDecodeBHist tail)

private theorem bishopCompletionTheoremDecode_encode_bhist :
    ∀ h : BHist,
      bishopCompletionTheoremDecodeBHist (bishopCompletionTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def bishopCompletionTheoremToEventFlow : BishopCompletionTheoremUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCompletionTheoremUp.mk modulus stream readback realSeal universalHandoff transport
      replay provenance name =>
      [[BMark.b0],
        bishopCompletionTheoremEncodeBHist modulus,
        [BMark.b1, BMark.b0],
        bishopCompletionTheoremEncodeBHist stream,
        [BMark.b1, BMark.b1, BMark.b0],
        bishopCompletionTheoremEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopCompletionTheoremEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopCompletionTheoremEncodeBHist universalHandoff,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopCompletionTheoremEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopCompletionTheoremEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        bishopCompletionTheoremEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        bishopCompletionTheoremEncodeBHist name]

def bishopCompletionTheoremFromEventFlow : EventFlow → Option BishopCompletionTheoremUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | modulus :: rest1 =>
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
                              | realSeal :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | universalHandoff :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | replay :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (BishopCompletionTheoremUp.mk
                                                                                  (bishopCompletionTheoremDecodeBHist
                                                                                    modulus)
                                                                                  (bishopCompletionTheoremDecodeBHist
                                                                                    stream)
                                                                                  (bishopCompletionTheoremDecodeBHist
                                                                                    readback)
                                                                                  (bishopCompletionTheoremDecodeBHist
                                                                                    realSeal)
                                                                                  (bishopCompletionTheoremDecodeBHist
                                                                                    universalHandoff)
                                                                                  (bishopCompletionTheoremDecodeBHist
                                                                                    transport)
                                                                                  (bishopCompletionTheoremDecodeBHist
                                                                                    replay)
                                                                                  (bishopCompletionTheoremDecodeBHist
                                                                                    provenance)
                                                                                  (bishopCompletionTheoremDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem bishopCompletionTheorem_round_trip :
    ∀ x : BishopCompletionTheoremUp,
      bishopCompletionTheoremFromEventFlow (bishopCompletionTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk modulus stream readback realSeal universalHandoff transport replay provenance name =>
      change
        some
          (BishopCompletionTheoremUp.mk
            (bishopCompletionTheoremDecodeBHist (bishopCompletionTheoremEncodeBHist modulus))
            (bishopCompletionTheoremDecodeBHist (bishopCompletionTheoremEncodeBHist stream))
            (bishopCompletionTheoremDecodeBHist (bishopCompletionTheoremEncodeBHist readback))
            (bishopCompletionTheoremDecodeBHist (bishopCompletionTheoremEncodeBHist realSeal))
            (bishopCompletionTheoremDecodeBHist
              (bishopCompletionTheoremEncodeBHist universalHandoff))
            (bishopCompletionTheoremDecodeBHist (bishopCompletionTheoremEncodeBHist transport))
            (bishopCompletionTheoremDecodeBHist (bishopCompletionTheoremEncodeBHist replay))
            (bishopCompletionTheoremDecodeBHist (bishopCompletionTheoremEncodeBHist provenance))
            (bishopCompletionTheoremDecodeBHist (bishopCompletionTheoremEncodeBHist name))) =
          some
            (BishopCompletionTheoremUp.mk modulus stream readback realSeal universalHandoff
              transport replay provenance name)
      rw [bishopCompletionTheoremDecode_encode_bhist modulus,
        bishopCompletionTheoremDecode_encode_bhist stream,
        bishopCompletionTheoremDecode_encode_bhist readback,
        bishopCompletionTheoremDecode_encode_bhist realSeal,
        bishopCompletionTheoremDecode_encode_bhist universalHandoff,
        bishopCompletionTheoremDecode_encode_bhist transport,
        bishopCompletionTheoremDecode_encode_bhist replay,
        bishopCompletionTheoremDecode_encode_bhist provenance,
        bishopCompletionTheoremDecode_encode_bhist name]

private theorem bishopCompletionTheoremToEventFlow_injective {x y : BishopCompletionTheoremUp} :
    bishopCompletionTheoremToEventFlow x = bishopCompletionTheoremToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCompletionTheoremFromEventFlow (bishopCompletionTheoremToEventFlow x) =
        bishopCompletionTheoremFromEventFlow (bishopCompletionTheoremToEventFlow y) :=
    congrArg bishopCompletionTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopCompletionTheorem_round_trip x).symm
      (Eq.trans hread (bishopCompletionTheorem_round_trip y)))

instance bishopCompletionTheoremBHistCarrier : BHistCarrier BishopCompletionTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCompletionTheoremToEventFlow
  fromEventFlow := bishopCompletionTheoremFromEventFlow

instance bishopCompletionTheoremChapterTasteGate :
    ChapterTasteGate BishopCompletionTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopCompletionTheoremFromEventFlow (bishopCompletionTheoremToEventFlow x) = some x
    exact bishopCompletionTheorem_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopCompletionTheoremToEventFlow_injective heq)

theorem BishopCompletionTheoremTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopCompletionTheoremDecodeBHist (bishopCompletionTheoremEncodeBHist h) = h) ∧
      (∀ x : BishopCompletionTheoremUp,
        bishopCompletionTheoremFromEventFlow (bishopCompletionTheoremToEventFlow x) = some x) ∧
      (∀ x y : BishopCompletionTheoremUp,
        bishopCompletionTheoremToEventFlow x = bishopCompletionTheoremToEventFlow y → x = y) ∧
      bishopCompletionTheoremEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact bishopCompletionTheoremDecode_encode_bhist
  · constructor
    · exact bishopCompletionTheorem_round_trip
    · constructor
      · intro x y heq
        exact bishopCompletionTheoremToEventFlow_injective heq
      · rfl

end BEDC.Derived.BishopCompletionTheoremUp
