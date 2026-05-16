import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContinuationCountermodelUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContinuationCountermodelUp : Type where
  | mk : (F U M O K S E H R P N : BHist) -> ContinuationCountermodelUp

def continuationCountermodelEncodeBHist : BHist -> List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: continuationCountermodelEncodeBHist h
  | BHist.e1 h => BMark.b1 :: continuationCountermodelEncodeBHist h

def continuationCountermodelDecodeBHist : List BMark -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (continuationCountermodelDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (continuationCountermodelDecodeBHist tail)

private theorem continuationCountermodel_decode_encode_bhist :
    forall h : BHist,
      continuationCountermodelDecodeBHist (continuationCountermodelEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def continuationCountermodelToEventFlow : ContinuationCountermodelUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ContinuationCountermodelUp.mk F U M O K S E H R P N =>
      [[BMark.b0],
        continuationCountermodelEncodeBHist F,
        [BMark.b1, BMark.b0],
        continuationCountermodelEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b0],
        continuationCountermodelEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        continuationCountermodelEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        continuationCountermodelEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        continuationCountermodelEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        continuationCountermodelEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        continuationCountermodelEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        continuationCountermodelEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        continuationCountermodelEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        continuationCountermodelEncodeBHist N]

def continuationCountermodelFromEventFlow : EventFlow -> Option ContinuationCountermodelUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | F :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | U :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | M :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | O :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | K :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | S :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | E :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | H :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | R :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | P :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | N :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (ContinuationCountermodelUp.mk
                                                                                                  (continuationCountermodelDecodeBHist F)
                                                                                                  (continuationCountermodelDecodeBHist U)
                                                                                                  (continuationCountermodelDecodeBHist M)
                                                                                                  (continuationCountermodelDecodeBHist O)
                                                                                                  (continuationCountermodelDecodeBHist K)
                                                                                                  (continuationCountermodelDecodeBHist S)
                                                                                                  (continuationCountermodelDecodeBHist E)
                                                                                                  (continuationCountermodelDecodeBHist H)
                                                                                                  (continuationCountermodelDecodeBHist R)
                                                                                                  (continuationCountermodelDecodeBHist P)
                                                                                                  (continuationCountermodelDecodeBHist N))
                                                                                          | _ :: _ => none

private theorem continuationCountermodel_round_trip :
    forall x : ContinuationCountermodelUp,
      continuationCountermodelFromEventFlow (continuationCountermodelToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F U M O K S E H R P N =>
      change
        some
          (ContinuationCountermodelUp.mk
            (continuationCountermodelDecodeBHist (continuationCountermodelEncodeBHist F))
            (continuationCountermodelDecodeBHist (continuationCountermodelEncodeBHist U))
            (continuationCountermodelDecodeBHist (continuationCountermodelEncodeBHist M))
            (continuationCountermodelDecodeBHist (continuationCountermodelEncodeBHist O))
            (continuationCountermodelDecodeBHist (continuationCountermodelEncodeBHist K))
            (continuationCountermodelDecodeBHist (continuationCountermodelEncodeBHist S))
            (continuationCountermodelDecodeBHist (continuationCountermodelEncodeBHist E))
            (continuationCountermodelDecodeBHist (continuationCountermodelEncodeBHist H))
            (continuationCountermodelDecodeBHist (continuationCountermodelEncodeBHist R))
            (continuationCountermodelDecodeBHist (continuationCountermodelEncodeBHist P))
            (continuationCountermodelDecodeBHist (continuationCountermodelEncodeBHist N))) =
          some (ContinuationCountermodelUp.mk F U M O K S E H R P N)
      rw [continuationCountermodel_decode_encode_bhist F,
        continuationCountermodel_decode_encode_bhist U,
        continuationCountermodel_decode_encode_bhist M,
        continuationCountermodel_decode_encode_bhist O,
        continuationCountermodel_decode_encode_bhist K,
        continuationCountermodel_decode_encode_bhist S,
        continuationCountermodel_decode_encode_bhist E,
        continuationCountermodel_decode_encode_bhist H,
        continuationCountermodel_decode_encode_bhist R,
        continuationCountermodel_decode_encode_bhist P,
        continuationCountermodel_decode_encode_bhist N]

private theorem continuationCountermodelToEventFlow_injective
    {x y : ContinuationCountermodelUp} :
    continuationCountermodelToEventFlow x = continuationCountermodelToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      continuationCountermodelFromEventFlow (continuationCountermodelToEventFlow x) =
        continuationCountermodelFromEventFlow (continuationCountermodelToEventFlow y) :=
    congrArg continuationCountermodelFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (continuationCountermodel_round_trip x).symm
      (Eq.trans hread (continuationCountermodel_round_trip y)))

private def continuationCountermodelFields : ContinuationCountermodelUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ContinuationCountermodelUp.mk F U M O K S E H R P N => [F, U, M, O, K, S, E, H, R, P, N]

private theorem continuationCountermodel_field_faithful :
    forall x y : ContinuationCountermodelUp,
      continuationCountermodelFields x = continuationCountermodelFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F U M O K S E H R P N =>
      cases y with
      | mk F' U' M' O' K' S' E' H' R' P' N' =>
          cases hfields
          rfl

instance continuationCountermodelBHistCarrier : BHistCarrier ContinuationCountermodelUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := continuationCountermodelToEventFlow
  fromEventFlow := continuationCountermodelFromEventFlow

instance continuationCountermodelChapterTasteGateInstance :
    ChapterTasteGate ContinuationCountermodelUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change continuationCountermodelFromEventFlow (continuationCountermodelToEventFlow x) = some x
    exact continuationCountermodel_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (continuationCountermodelToEventFlow_injective heq)

instance continuationCountermodelFieldFaithful : FieldFaithful ContinuationCountermodelUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := continuationCountermodelFields
  field_faithful := continuationCountermodel_field_faithful

instance continuationCountermodelNontrivial : Nontrivial ContinuationCountermodelUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ContinuationCountermodelUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ContinuationCountermodelUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def continuationCountermodelChapterTasteGate :
    ChapterTasteGate ContinuationCountermodelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  continuationCountermodelChapterTasteGateInstance

def taste_gate : ChapterTasteGate ContinuationCountermodelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  continuationCountermodelChapterTasteGate

theorem ContinuationCountermodelTasteGate_single_carrier_alignment :
    (forall h : BHist,
      continuationCountermodelDecodeBHist (continuationCountermodelEncodeBHist h) = h) ∧
      (forall x : ContinuationCountermodelUp,
        continuationCountermodelFromEventFlow (continuationCountermodelToEventFlow x) = some x) ∧
        (forall x y : ContinuationCountermodelUp,
          continuationCountermodelToEventFlow x = continuationCountermodelToEventFlow y -> x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨continuationCountermodel_decode_encode_bhist, continuationCountermodel_round_trip,
      (by
        intro x y heq
        exact continuationCountermodelToEventFlow_injective heq)⟩

end BEDC.Derived.ContinuationCountermodelUp
