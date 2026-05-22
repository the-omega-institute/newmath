import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedUniformCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedUniformCompletionUp : Type where
  | mk : (F U B S R E H C P N : BHist) → LocatedUniformCompletionUp
  deriving DecidableEq

def locatedUniformCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedUniformCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedUniformCompletionEncodeBHist h

def locatedUniformCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedUniformCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedUniformCompletionDecodeBHist tail)

private theorem locatedUniformCompletion_decode_encode_bhist :
    ∀ h : BHist,
      locatedUniformCompletionDecodeBHist (locatedUniformCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def locatedUniformCompletionToEventFlow :
    LocatedUniformCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedUniformCompletionUp.mk F U B S R E H C P N =>
      [[BMark.b0],
        locatedUniformCompletionEncodeBHist F,
        [BMark.b1, BMark.b0],
        locatedUniformCompletionEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b0],
        locatedUniformCompletionEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedUniformCompletionEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedUniformCompletionEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedUniformCompletionEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedUniformCompletionEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        locatedUniformCompletionEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        locatedUniformCompletionEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        locatedUniformCompletionEncodeBHist N]

def locatedUniformCompletionFromEventFlow :
    EventFlow → Option LocatedUniformCompletionUp
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
                      | B :: rest5 =>
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
                                                                                        (LocatedUniformCompletionUp.mk
                                                                                          (locatedUniformCompletionDecodeBHist F)
                                                                                          (locatedUniformCompletionDecodeBHist U)
                                                                                          (locatedUniformCompletionDecodeBHist B)
                                                                                          (locatedUniformCompletionDecodeBHist S)
                                                                                          (locatedUniformCompletionDecodeBHist R)
                                                                                          (locatedUniformCompletionDecodeBHist E)
                                                                                          (locatedUniformCompletionDecodeBHist H)
                                                                                          (locatedUniformCompletionDecodeBHist C)
                                                                                          (locatedUniformCompletionDecodeBHist P)
                                                                                          (locatedUniformCompletionDecodeBHist N))
                                                                                  | _ :: _ => none

private theorem locatedUniformCompletion_round_trip :
    ∀ x : LocatedUniformCompletionUp,
      locatedUniformCompletionFromEventFlow (locatedUniformCompletionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F U B S R E H C P N =>
      change
        some
          (LocatedUniformCompletionUp.mk
            (locatedUniformCompletionDecodeBHist (locatedUniformCompletionEncodeBHist F))
            (locatedUniformCompletionDecodeBHist (locatedUniformCompletionEncodeBHist U))
            (locatedUniformCompletionDecodeBHist (locatedUniformCompletionEncodeBHist B))
            (locatedUniformCompletionDecodeBHist (locatedUniformCompletionEncodeBHist S))
            (locatedUniformCompletionDecodeBHist (locatedUniformCompletionEncodeBHist R))
            (locatedUniformCompletionDecodeBHist (locatedUniformCompletionEncodeBHist E))
            (locatedUniformCompletionDecodeBHist (locatedUniformCompletionEncodeBHist H))
            (locatedUniformCompletionDecodeBHist (locatedUniformCompletionEncodeBHist C))
            (locatedUniformCompletionDecodeBHist (locatedUniformCompletionEncodeBHist P))
            (locatedUniformCompletionDecodeBHist (locatedUniformCompletionEncodeBHist N))) =
          some (LocatedUniformCompletionUp.mk F U B S R E H C P N)
      rw [locatedUniformCompletion_decode_encode_bhist F,
        locatedUniformCompletion_decode_encode_bhist U,
        locatedUniformCompletion_decode_encode_bhist B,
        locatedUniformCompletion_decode_encode_bhist S,
        locatedUniformCompletion_decode_encode_bhist R,
        locatedUniformCompletion_decode_encode_bhist E,
        locatedUniformCompletion_decode_encode_bhist H,
        locatedUniformCompletion_decode_encode_bhist C,
        locatedUniformCompletion_decode_encode_bhist P,
        locatedUniformCompletion_decode_encode_bhist N]

private theorem locatedUniformCompletionToEventFlow_injective
    {x y : LocatedUniformCompletionUp} :
    locatedUniformCompletionToEventFlow x = locatedUniformCompletionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedUniformCompletionFromEventFlow (locatedUniformCompletionToEventFlow x) =
        locatedUniformCompletionFromEventFlow (locatedUniformCompletionToEventFlow y) :=
    congrArg locatedUniformCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedUniformCompletion_round_trip x).symm
      (Eq.trans hread (locatedUniformCompletion_round_trip y)))

instance locatedUniformCompletionBHistCarrier :
    BHistCarrier LocatedUniformCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedUniformCompletionToEventFlow
  fromEventFlow := locatedUniformCompletionFromEventFlow

instance locatedUniformCompletionChapterTasteGate :
    ChapterTasteGate LocatedUniformCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedUniformCompletionFromEventFlow (locatedUniformCompletionToEventFlow x) = some x
    exact locatedUniformCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedUniformCompletionToEventFlow_injective heq)

instance locatedUniformCompletionFieldFaithful :
    FieldFaithful LocatedUniformCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | LocatedUniformCompletionUp.mk F U B S R E H C P N => [F, U, B, S, R, E, H, C, P, N]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk F1 U1 B1 S1 R1 E1 H1 C1 P1 N1 =>
        cases y with
        | mk F2 U2 B2 S2 R2 E2 H2 C2 P2 N2 =>
            injection hfields with hF t1
            cases hF
            injection t1 with hU t2
            cases hU
            injection t2 with hB t3
            cases hB
            injection t3 with hS t4
            cases hS
            injection t4 with hR t5
            cases hR
            injection t5 with hE t6
            cases hE
            injection t6 with hH t7
            cases hH
            injection t7 with hC t8
            cases hC
            injection t8 with hP t9
            cases hP
            injection t9 with hN _
            cases hN
            rfl

namespace TasteGate

theorem LocatedUniformCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedUniformCompletionDecodeBHist (locatedUniformCompletionEncodeBHist h) = h) ∧
      (∀ x : LocatedUniformCompletionUp,
        locatedUniformCompletionFromEventFlow (locatedUniformCompletionToEventFlow x) = some x) ∧
        (∀ x y : LocatedUniformCompletionUp,
          locatedUniformCompletionToEventFlow x = locatedUniformCompletionToEventFlow y →
            x = y) ∧
          locatedUniformCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact locatedUniformCompletion_decode_encode_bhist
  · constructor
    · exact locatedUniformCompletion_round_trip
    · constructor
      · intro x y heq
        exact locatedUniformCompletionToEventFlow_injective heq
      · rfl

end TasteGate

end BEDC.Derived.LocatedUniformCompletionUp
