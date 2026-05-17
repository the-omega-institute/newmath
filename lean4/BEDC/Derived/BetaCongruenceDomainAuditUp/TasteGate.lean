import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BetaCongruenceDomainAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BetaCongruenceDomainAuditUp : Type where
  | mk (T M Pi R S H K P N : BHist) : BetaCongruenceDomainAuditUp
  deriving DecidableEq

def betaCongruenceDomainAuditEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: betaCongruenceDomainAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: betaCongruenceDomainAuditEncodeBHist h

def betaCongruenceDomainAuditDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (betaCongruenceDomainAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (betaCongruenceDomainAuditDecodeBHist tail)

private theorem betaCongruenceDomainAuditDecode_encode_bhist :
    forall h : BHist,
      betaCongruenceDomainAuditDecodeBHist
          (betaCongruenceDomainAuditEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def betaCongruenceDomainAuditToEventFlow : BetaCongruenceDomainAuditUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BetaCongruenceDomainAuditUp.mk T M Pi R S H K P N =>
      [[BMark.b0],
        betaCongruenceDomainAuditEncodeBHist T,
        [BMark.b1, BMark.b0],
        betaCongruenceDomainAuditEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b0],
        betaCongruenceDomainAuditEncodeBHist Pi,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        betaCongruenceDomainAuditEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        betaCongruenceDomainAuditEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        betaCongruenceDomainAuditEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        betaCongruenceDomainAuditEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        betaCongruenceDomainAuditEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        betaCongruenceDomainAuditEncodeBHist N]

private def betaCongruenceDomainAuditDecodePacket
    (T M Pi R S H K P N : RawEvent) : BetaCongruenceDomainAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BetaCongruenceDomainAuditUp.mk
    (betaCongruenceDomainAuditDecodeBHist T)
    (betaCongruenceDomainAuditDecodeBHist M)
    (betaCongruenceDomainAuditDecodeBHist Pi)
    (betaCongruenceDomainAuditDecodeBHist R)
    (betaCongruenceDomainAuditDecodeBHist S)
    (betaCongruenceDomainAuditDecodeBHist H)
    (betaCongruenceDomainAuditDecodeBHist K)
    (betaCongruenceDomainAuditDecodeBHist P)
    (betaCongruenceDomainAuditDecodeBHist N)

def betaCongruenceDomainAuditFromEventFlow : EventFlow -> Option BetaCongruenceDomainAuditUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | T :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | M :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | Pi :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | R :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | S :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | H :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | K :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | P :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | N :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (betaCongruenceDomainAuditDecodePacket
                                                                                  T M Pi R S H K P N)
                                                                          | _ :: _ => none

private theorem betaCongruenceDomainAudit_round_trip :
    forall x : BetaCongruenceDomainAuditUp,
      betaCongruenceDomainAuditFromEventFlow
          (betaCongruenceDomainAuditToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T M Pi R S H K P N =>
      change
        some
          (betaCongruenceDomainAuditDecodePacket
            (betaCongruenceDomainAuditEncodeBHist T)
            (betaCongruenceDomainAuditEncodeBHist M)
            (betaCongruenceDomainAuditEncodeBHist Pi)
            (betaCongruenceDomainAuditEncodeBHist R)
            (betaCongruenceDomainAuditEncodeBHist S)
            (betaCongruenceDomainAuditEncodeBHist H)
            (betaCongruenceDomainAuditEncodeBHist K)
            (betaCongruenceDomainAuditEncodeBHist P)
            (betaCongruenceDomainAuditEncodeBHist N)) =
          some (BetaCongruenceDomainAuditUp.mk T M Pi R S H K P N)
      unfold betaCongruenceDomainAuditDecodePacket
      rw [betaCongruenceDomainAuditDecode_encode_bhist T,
        betaCongruenceDomainAuditDecode_encode_bhist M,
        betaCongruenceDomainAuditDecode_encode_bhist Pi,
        betaCongruenceDomainAuditDecode_encode_bhist R,
        betaCongruenceDomainAuditDecode_encode_bhist S,
        betaCongruenceDomainAuditDecode_encode_bhist H,
        betaCongruenceDomainAuditDecode_encode_bhist K,
        betaCongruenceDomainAuditDecode_encode_bhist P,
        betaCongruenceDomainAuditDecode_encode_bhist N]

private theorem betaCongruenceDomainAuditToEventFlow_injective
    {x y : BetaCongruenceDomainAuditUp} :
    betaCongruenceDomainAuditToEventFlow x = betaCongruenceDomainAuditToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      betaCongruenceDomainAuditFromEventFlow (betaCongruenceDomainAuditToEventFlow x) =
        betaCongruenceDomainAuditFromEventFlow (betaCongruenceDomainAuditToEventFlow y) :=
    congrArg betaCongruenceDomainAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (betaCongruenceDomainAudit_round_trip x).symm
      (Eq.trans hread (betaCongruenceDomainAudit_round_trip y)))

private def betaCongruenceDomainAuditFields :
    BetaCongruenceDomainAuditUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BetaCongruenceDomainAuditUp.mk T M Pi R S H K P N => [T, M, Pi, R, S, H, K, P, N]

private theorem betaCongruenceDomainAudit_fields_faithful :
    forall x y : BetaCongruenceDomainAuditUp,
      betaCongruenceDomainAuditFields x = betaCongruenceDomainAuditFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T1 M1 Pi1 R1 S1 H1 K1 P1 N1 =>
      cases y with
      | mk T2 M2 Pi2 R2 S2 H2 K2 P2 N2 =>
          cases hfields
          rfl

instance betaCongruenceDomainAuditBHistCarrier :
    BHistCarrier BetaCongruenceDomainAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := betaCongruenceDomainAuditToEventFlow
  fromEventFlow := betaCongruenceDomainAuditFromEventFlow

instance betaCongruenceDomainAuditChapterTasteGate :
    ChapterTasteGate BetaCongruenceDomainAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      betaCongruenceDomainAuditFromEventFlow (betaCongruenceDomainAuditToEventFlow x) =
        some x
    exact betaCongruenceDomainAudit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (betaCongruenceDomainAuditToEventFlow_injective heq)

instance betaCongruenceDomainAuditFieldFaithful :
    FieldFaithful BetaCongruenceDomainAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := betaCongruenceDomainAuditFields
  field_faithful := betaCongruenceDomainAudit_fields_faithful

instance betaCongruenceDomainAuditNontrivial :
    Nontrivial BetaCongruenceDomainAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BetaCongruenceDomainAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BetaCongruenceDomainAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BetaCongruenceDomainAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  betaCongruenceDomainAuditChapterTasteGate

theorem BetaCongruenceDomainAuditTasteGate_single_carrier_alignment :
    betaCongruenceDomainAuditEncodeBHist BHist.Empty = [] ∧
      betaCongruenceDomainAuditEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
        (forall h : BHist,
          betaCongruenceDomainAuditDecodeBHist
              (betaCongruenceDomainAuditEncodeBHist h) =
            h) ∧
          (forall x : BetaCongruenceDomainAuditUp,
            betaCongruenceDomainAuditFromEventFlow
                (betaCongruenceDomainAuditToEventFlow x) =
              some x) ∧
            (forall x y : BetaCongruenceDomainAuditUp,
              betaCongruenceDomainAuditToEventFlow x =
                  betaCongruenceDomainAuditToEventFlow y ->
                x = y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨rfl, rfl, betaCongruenceDomainAuditDecode_encode_bhist,
      betaCongruenceDomainAudit_round_trip,
      fun _ _ heq => betaCongruenceDomainAuditToEventFlow_injective heq⟩

end BEDC.Derived.BetaCongruenceDomainAuditUp
