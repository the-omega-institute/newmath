import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyTailConsensusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyTailConsensusUp : Type where
  | mk : (S A L W R E H C P N : BHist) -> CauchyTailConsensusUp

def cauchyTailConsensusEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyTailConsensusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyTailConsensusEncodeBHist h

def cauchyTailConsensusDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyTailConsensusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyTailConsensusDecodeBHist tail)

private theorem cauchyTailConsensus_decode_encode_bhist :
    forall h : BHist, cauchyTailConsensusDecodeBHist
      (cauchyTailConsensusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyTailConsensusToEventFlow : CauchyTailConsensusUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyTailConsensusUp.mk S A L W R E H C P N =>
      [[BMark.b0],
        cauchyTailConsensusEncodeBHist S,
        [BMark.b1, BMark.b0],
        cauchyTailConsensusEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b0],
        cauchyTailConsensusEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyTailConsensusEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyTailConsensusEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyTailConsensusEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyTailConsensusEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cauchyTailConsensusEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        cauchyTailConsensusEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        cauchyTailConsensusEncodeBHist N]

def cauchyTailConsensusFromEventFlow : EventFlow -> Option CauchyTailConsensusUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | A :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | L :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | W :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | R :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | E :: rest11 =>
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
                                                                                        (CauchyTailConsensusUp.mk
                                                                                          (cauchyTailConsensusDecodeBHist S)
                                                                                          (cauchyTailConsensusDecodeBHist A)
                                                                                          (cauchyTailConsensusDecodeBHist L)
                                                                                          (cauchyTailConsensusDecodeBHist W)
                                                                                          (cauchyTailConsensusDecodeBHist R)
                                                                                          (cauchyTailConsensusDecodeBHist E)
                                                                                          (cauchyTailConsensusDecodeBHist H)
                                                                                          (cauchyTailConsensusDecodeBHist C)
                                                                                          (cauchyTailConsensusDecodeBHist P)
                                                                                          (cauchyTailConsensusDecodeBHist N))
                                                                                  | _ :: _ => none

private theorem cauchyTailConsensus_round_trip :
    forall x : CauchyTailConsensusUp,
      cauchyTailConsensusFromEventFlow (cauchyTailConsensusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S A L W R E H C P N =>
      change
        some
          (CauchyTailConsensusUp.mk
            (cauchyTailConsensusDecodeBHist (cauchyTailConsensusEncodeBHist S))
            (cauchyTailConsensusDecodeBHist (cauchyTailConsensusEncodeBHist A))
            (cauchyTailConsensusDecodeBHist (cauchyTailConsensusEncodeBHist L))
            (cauchyTailConsensusDecodeBHist (cauchyTailConsensusEncodeBHist W))
            (cauchyTailConsensusDecodeBHist (cauchyTailConsensusEncodeBHist R))
            (cauchyTailConsensusDecodeBHist (cauchyTailConsensusEncodeBHist E))
            (cauchyTailConsensusDecodeBHist (cauchyTailConsensusEncodeBHist H))
            (cauchyTailConsensusDecodeBHist (cauchyTailConsensusEncodeBHist C))
            (cauchyTailConsensusDecodeBHist (cauchyTailConsensusEncodeBHist P))
            (cauchyTailConsensusDecodeBHist (cauchyTailConsensusEncodeBHist N))) =
          some (CauchyTailConsensusUp.mk S A L W R E H C P N)
      rw [cauchyTailConsensus_decode_encode_bhist S,
        cauchyTailConsensus_decode_encode_bhist A,
        cauchyTailConsensus_decode_encode_bhist L,
        cauchyTailConsensus_decode_encode_bhist W,
        cauchyTailConsensus_decode_encode_bhist R,
        cauchyTailConsensus_decode_encode_bhist E,
        cauchyTailConsensus_decode_encode_bhist H,
        cauchyTailConsensus_decode_encode_bhist C,
        cauchyTailConsensus_decode_encode_bhist P,
        cauchyTailConsensus_decode_encode_bhist N]

private theorem cauchyTailConsensusToEventFlow_injective {x y : CauchyTailConsensusUp} :
    cauchyTailConsensusToEventFlow x = cauchyTailConsensusToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyTailConsensusFromEventFlow (cauchyTailConsensusToEventFlow x) =
        cauchyTailConsensusFromEventFlow (cauchyTailConsensusToEventFlow y) :=
    congrArg cauchyTailConsensusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyTailConsensus_round_trip x).symm
      (Eq.trans hread (cauchyTailConsensus_round_trip y)))

private def cauchyTailConsensusFields : CauchyTailConsensusUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyTailConsensusUp.mk S A L W R E H C P N => [S, A, L, W, R, E, H, C, P, N]

private theorem cauchyTailConsensus_field_faithful :
    forall x y : CauchyTailConsensusUp,
      cauchyTailConsensusFields x = cauchyTailConsensusFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S A L W R E H C P N =>
      cases y with
      | mk S' A' L' W' R' E' H' C' P' N' =>
          cases hfields
          rfl

instance cauchyTailConsensusBHistCarrier : BHistCarrier CauchyTailConsensusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyTailConsensusToEventFlow
  fromEventFlow := cauchyTailConsensusFromEventFlow

instance cauchyTailConsensusChapterTasteGate : ChapterTasteGate CauchyTailConsensusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyTailConsensusFromEventFlow (cauchyTailConsensusToEventFlow x) = some x
    exact cauchyTailConsensus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyTailConsensusToEventFlow_injective heq)

instance cauchyTailConsensusFieldFaithful : FieldFaithful CauchyTailConsensusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyTailConsensusFields
  field_faithful := cauchyTailConsensus_field_faithful

def taste_gate : ChapterTasteGate CauchyTailConsensusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyTailConsensusChapterTasteGate

theorem CauchyTailConsensusTasteGate_single_carrier_alignment :
    (forall h : BHist, cauchyTailConsensusDecodeBHist
      (cauchyTailConsensusEncodeBHist h) = h) ∧
      (forall x : CauchyTailConsensusUp,
        cauchyTailConsensusFromEventFlow (cauchyTailConsensusToEventFlow x) = some x) ∧
        (forall x y : CauchyTailConsensusUp,
          cauchyTailConsensusToEventFlow x = cauchyTailConsensusToEventFlow y -> x = y) ∧
          cauchyTailConsensusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨cauchyTailConsensus_decode_encode_bhist, cauchyTailConsensus_round_trip,
      (by
        intro x y heq
        exact cauchyTailConsensusToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyTailConsensusUp
