import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GroundCompilerAuditPacketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GroundCompilerAuditPacketUp : Type where
  | mk : (E S R C Q M B X H T P N : BHist) → GroundCompilerAuditPacketUp
  deriving DecidableEq

def groundCompilerAuditPacketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: groundCompilerAuditPacketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: groundCompilerAuditPacketEncodeBHist h

def groundCompilerAuditPacketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (groundCompilerAuditPacketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (groundCompilerAuditPacketDecodeBHist tail)

private theorem groundCompilerAuditPacketDecode_encode_bhist :
    ∀ h : BHist,
      groundCompilerAuditPacketDecodeBHist
        (groundCompilerAuditPacketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def groundCompilerAuditPacketToEventFlow : GroundCompilerAuditPacketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | GroundCompilerAuditPacketUp.mk E S R C Q M B X H T P N =>
      [[BMark.b0],
        groundCompilerAuditPacketEncodeBHist E,
        [BMark.b1, BMark.b0],
        groundCompilerAuditPacketEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b0],
        groundCompilerAuditPacketEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerAuditPacketEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerAuditPacketEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerAuditPacketEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerAuditPacketEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        groundCompilerAuditPacketEncodeBHist X,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        groundCompilerAuditPacketEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        groundCompilerAuditPacketEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerAuditPacketEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerAuditPacketEncodeBHist N]

def groundCompilerAuditPacketFromEventFlow : EventFlow → Option GroundCompilerAuditPacketUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | E :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | S :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
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
                                              | M :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | B :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | X :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | H :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | T :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | P :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] => none
                                                                                          | _tag11 :: rest22 =>
                                                                                              match rest22 with
                                                                                              | [] => none
                                                                                              | N :: rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] =>
                                                                                                      some
                                                                                                        (GroundCompilerAuditPacketUp.mk
                                                                                                          (groundCompilerAuditPacketDecodeBHist E)
                                                                                                          (groundCompilerAuditPacketDecodeBHist S)
                                                                                                          (groundCompilerAuditPacketDecodeBHist R)
                                                                                                          (groundCompilerAuditPacketDecodeBHist C)
                                                                                                          (groundCompilerAuditPacketDecodeBHist Q)
                                                                                                          (groundCompilerAuditPacketDecodeBHist M)
                                                                                                          (groundCompilerAuditPacketDecodeBHist B)
                                                                                                          (groundCompilerAuditPacketDecodeBHist X)
                                                                                                          (groundCompilerAuditPacketDecodeBHist H)
                                                                                                          (groundCompilerAuditPacketDecodeBHist T)
                                                                                                          (groundCompilerAuditPacketDecodeBHist P)
                                                                                                          (groundCompilerAuditPacketDecodeBHist N))
                                                                                                  | _ :: _ => none

private theorem groundCompilerAuditPacket_round_trip :
    ∀ x : GroundCompilerAuditPacketUp,
      groundCompilerAuditPacketFromEventFlow
        (groundCompilerAuditPacketToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E S R C Q M B X H T P N =>
      change
        some
          (GroundCompilerAuditPacketUp.mk
            (groundCompilerAuditPacketDecodeBHist (groundCompilerAuditPacketEncodeBHist E))
            (groundCompilerAuditPacketDecodeBHist (groundCompilerAuditPacketEncodeBHist S))
            (groundCompilerAuditPacketDecodeBHist (groundCompilerAuditPacketEncodeBHist R))
            (groundCompilerAuditPacketDecodeBHist (groundCompilerAuditPacketEncodeBHist C))
            (groundCompilerAuditPacketDecodeBHist (groundCompilerAuditPacketEncodeBHist Q))
            (groundCompilerAuditPacketDecodeBHist (groundCompilerAuditPacketEncodeBHist M))
            (groundCompilerAuditPacketDecodeBHist (groundCompilerAuditPacketEncodeBHist B))
            (groundCompilerAuditPacketDecodeBHist (groundCompilerAuditPacketEncodeBHist X))
            (groundCompilerAuditPacketDecodeBHist (groundCompilerAuditPacketEncodeBHist H))
            (groundCompilerAuditPacketDecodeBHist (groundCompilerAuditPacketEncodeBHist T))
            (groundCompilerAuditPacketDecodeBHist (groundCompilerAuditPacketEncodeBHist P))
            (groundCompilerAuditPacketDecodeBHist (groundCompilerAuditPacketEncodeBHist N))) =
          some (GroundCompilerAuditPacketUp.mk E S R C Q M B X H T P N)
      rw [groundCompilerAuditPacketDecode_encode_bhist E,
        groundCompilerAuditPacketDecode_encode_bhist S,
        groundCompilerAuditPacketDecode_encode_bhist R,
        groundCompilerAuditPacketDecode_encode_bhist C,
        groundCompilerAuditPacketDecode_encode_bhist Q,
        groundCompilerAuditPacketDecode_encode_bhist M,
        groundCompilerAuditPacketDecode_encode_bhist B,
        groundCompilerAuditPacketDecode_encode_bhist X,
        groundCompilerAuditPacketDecode_encode_bhist H,
        groundCompilerAuditPacketDecode_encode_bhist T,
        groundCompilerAuditPacketDecode_encode_bhist P,
        groundCompilerAuditPacketDecode_encode_bhist N]

private theorem groundCompilerAuditPacketToEventFlow_injective
    {x y : GroundCompilerAuditPacketUp} :
    groundCompilerAuditPacketToEventFlow x = groundCompilerAuditPacketToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      groundCompilerAuditPacketFromEventFlow (groundCompilerAuditPacketToEventFlow x) =
        groundCompilerAuditPacketFromEventFlow (groundCompilerAuditPacketToEventFlow y) :=
    congrArg groundCompilerAuditPacketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (groundCompilerAuditPacket_round_trip x).symm
      (Eq.trans hread (groundCompilerAuditPacket_round_trip y)))

instance groundCompilerAuditPacketBHistCarrier : BHistCarrier GroundCompilerAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := groundCompilerAuditPacketToEventFlow
  fromEventFlow := groundCompilerAuditPacketFromEventFlow

instance groundCompilerAuditPacketChapterTasteGate :
    ChapterTasteGate GroundCompilerAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change groundCompilerAuditPacketFromEventFlow
      (groundCompilerAuditPacketToEventFlow x) = some x
    exact groundCompilerAuditPacket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (groundCompilerAuditPacketToEventFlow_injective heq)

instance groundCompilerAuditPacketFieldFaithful :
    FieldFaithful GroundCompilerAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | GroundCompilerAuditPacketUp.mk E S R C Q M B X H T P N =>
        [E, S, R, C, Q, M, B, X, H, T, P, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk E1 S1 R1 C1 Q1 M1 B1 X1 H1 T1 P1 N1 =>
        cases y with
        | mk E2 S2 R2 C2 Q2 M2 B2 X2 H2 T2 P2 N2 =>
            cases h
            rfl

def taste_gate : ChapterTasteGate GroundCompilerAuditPacketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  groundCompilerAuditPacketChapterTasteGate

theorem GroundCompilerAuditPacketTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        groundCompilerAuditPacketDecodeBHist (groundCompilerAuditPacketEncodeBHist h) = h) ∧
      (∀ x : GroundCompilerAuditPacketUp,
        groundCompilerAuditPacketFromEventFlow
          (groundCompilerAuditPacketToEventFlow x) = some x) ∧
        (∀ x y : GroundCompilerAuditPacketUp,
          groundCompilerAuditPacketToEventFlow x = groundCompilerAuditPacketToEventFlow y →
            x = y) ∧
          groundCompilerAuditPacketEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact groundCompilerAuditPacketDecode_encode_bhist
  · constructor
    · intro x
      change groundCompilerAuditPacketFromEventFlow
        (groundCompilerAuditPacketToEventFlow x) = some x
      exact groundCompilerAuditPacket_round_trip x
    · constructor
      · intro x y heq
        exact groundCompilerAuditPacketToEventFlow_injective heq
      · rfl

end BEDC.Derived.GroundCompilerAuditPacketUp
