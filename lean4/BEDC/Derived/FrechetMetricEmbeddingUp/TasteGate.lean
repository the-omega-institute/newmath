import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FrechetMetricEmbeddingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FrechetMetricEmbeddingUp : Type where
  | mk (X Q D A H C P N : BHist) : FrechetMetricEmbeddingUp

def frechetMetricEmbeddingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: frechetMetricEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: frechetMetricEmbeddingEncodeBHist h

def frechetMetricEmbeddingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (frechetMetricEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (frechetMetricEmbeddingDecodeBHist tail)

private theorem frechetMetricEmbeddingDecode_encode_bhist :
    ∀ h : BHist,
      frechetMetricEmbeddingDecodeBHist (frechetMetricEmbeddingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def frechetMetricEmbeddingToEventFlow : FrechetMetricEmbeddingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FrechetMetricEmbeddingUp.mk X Q D A H C P N =>
      [[BMark.b0],
        frechetMetricEmbeddingEncodeBHist X,
        [BMark.b1, BMark.b0],
        frechetMetricEmbeddingEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b0],
        frechetMetricEmbeddingEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        frechetMetricEmbeddingEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        frechetMetricEmbeddingEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        frechetMetricEmbeddingEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        frechetMetricEmbeddingEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        frechetMetricEmbeddingEncodeBHist N]

def frechetMetricEmbeddingFromEventFlow : EventFlow → Option FrechetMetricEmbeddingUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | X :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | Q :: rest3 =>
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
                              | A :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | H :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | C :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | P :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | N :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (FrechetMetricEmbeddingUp.mk
                                                                          (frechetMetricEmbeddingDecodeBHist X)
                                                                          (frechetMetricEmbeddingDecodeBHist Q)
                                                                          (frechetMetricEmbeddingDecodeBHist D)
                                                                          (frechetMetricEmbeddingDecodeBHist A)
                                                                          (frechetMetricEmbeddingDecodeBHist H)
                                                                          (frechetMetricEmbeddingDecodeBHist C)
                                                                          (frechetMetricEmbeddingDecodeBHist P)
                                                                          (frechetMetricEmbeddingDecodeBHist N))
                                                                  | _ :: _ => none

private theorem frechetMetricEmbedding_round_trip :
    ∀ x : FrechetMetricEmbeddingUp,
      frechetMetricEmbeddingFromEventFlow (frechetMetricEmbeddingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Q D A H C P N =>
      change
        some
          (FrechetMetricEmbeddingUp.mk
            (frechetMetricEmbeddingDecodeBHist (frechetMetricEmbeddingEncodeBHist X))
            (frechetMetricEmbeddingDecodeBHist (frechetMetricEmbeddingEncodeBHist Q))
            (frechetMetricEmbeddingDecodeBHist (frechetMetricEmbeddingEncodeBHist D))
            (frechetMetricEmbeddingDecodeBHist (frechetMetricEmbeddingEncodeBHist A))
            (frechetMetricEmbeddingDecodeBHist (frechetMetricEmbeddingEncodeBHist H))
            (frechetMetricEmbeddingDecodeBHist (frechetMetricEmbeddingEncodeBHist C))
            (frechetMetricEmbeddingDecodeBHist (frechetMetricEmbeddingEncodeBHist P))
            (frechetMetricEmbeddingDecodeBHist (frechetMetricEmbeddingEncodeBHist N))) =
          some (FrechetMetricEmbeddingUp.mk X Q D A H C P N)
      rw [frechetMetricEmbeddingDecode_encode_bhist X,
        frechetMetricEmbeddingDecode_encode_bhist Q,
        frechetMetricEmbeddingDecode_encode_bhist D,
        frechetMetricEmbeddingDecode_encode_bhist A,
        frechetMetricEmbeddingDecode_encode_bhist H,
        frechetMetricEmbeddingDecode_encode_bhist C,
        frechetMetricEmbeddingDecode_encode_bhist P,
        frechetMetricEmbeddingDecode_encode_bhist N]

private theorem frechetMetricEmbeddingToEventFlow_injective
    {x y : FrechetMetricEmbeddingUp} :
    frechetMetricEmbeddingToEventFlow x = frechetMetricEmbeddingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      frechetMetricEmbeddingFromEventFlow (frechetMetricEmbeddingToEventFlow x) =
        frechetMetricEmbeddingFromEventFlow (frechetMetricEmbeddingToEventFlow y) :=
    congrArg frechetMetricEmbeddingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (frechetMetricEmbedding_round_trip x).symm
      (Eq.trans hread (frechetMetricEmbedding_round_trip y)))

instance frechetMetricEmbeddingBHistCarrier : BHistCarrier FrechetMetricEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := frechetMetricEmbeddingToEventFlow
  fromEventFlow := frechetMetricEmbeddingFromEventFlow

instance frechetMetricEmbeddingChapterTasteGate : ChapterTasteGate FrechetMetricEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change frechetMetricEmbeddingFromEventFlow (frechetMetricEmbeddingToEventFlow x) = some x
    exact frechetMetricEmbedding_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (frechetMetricEmbeddingToEventFlow_injective heq)

def taste_gate : ChapterTasteGate FrechetMetricEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  frechetMetricEmbeddingChapterTasteGate

theorem FrechetMetricEmbeddingTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      frechetMetricEmbeddingDecodeBHist (frechetMetricEmbeddingEncodeBHist h) = h) ∧
      (∀ x : FrechetMetricEmbeddingUp,
        frechetMetricEmbeddingFromEventFlow (frechetMetricEmbeddingToEventFlow x) = some x) ∧
      (∀ x y : FrechetMetricEmbeddingUp,
        frechetMetricEmbeddingToEventFlow x = frechetMetricEmbeddingToEventFlow y → x = y) ∧
      frechetMetricEmbeddingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact frechetMetricEmbeddingDecode_encode_bhist
  · constructor
    · exact frechetMetricEmbedding_round_trip
    · constructor
      · intro x y heq
        exact frechetMetricEmbeddingToEventFlow_injective heq
      · rfl

end BEDC.Derived.FrechetMetricEmbeddingUp
