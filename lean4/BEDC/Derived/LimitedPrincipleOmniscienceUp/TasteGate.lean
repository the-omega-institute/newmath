import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LimitedPrincipleOmniscienceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LimitedPrincipleOmniscienceUp : Type where
  | mk (A S R D E T H C P N : BHist) : LimitedPrincipleOmniscienceUp
  deriving DecidableEq

def limitedPrincipleOmniscienceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: limitedPrincipleOmniscienceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: limitedPrincipleOmniscienceEncodeBHist h

def limitedPrincipleOmniscienceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (limitedPrincipleOmniscienceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (limitedPrincipleOmniscienceDecodeBHist tail)

def limitedPrincipleOmniscienceFields : LimitedPrincipleOmniscienceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LimitedPrincipleOmniscienceUp.mk A S R D E T H C P N => [A, S, R, D, E, T, H, C, P, N]

private theorem limitedPrincipleOmniscience_decode_encode_bhist :
    ∀ h : BHist,
      limitedPrincipleOmniscienceDecodeBHist (limitedPrincipleOmniscienceEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def limitedPrincipleOmniscienceToEventFlow : LimitedPrincipleOmniscienceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (limitedPrincipleOmniscienceFields x).map limitedPrincipleOmniscienceEncodeBHist

def limitedPrincipleOmniscienceFromEventFlow :
    EventFlow → Option LimitedPrincipleOmniscienceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | A :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | R :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | E :: rest4 =>
                      match rest4 with
                      | [] => none
                      | T :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (LimitedPrincipleOmniscienceUp.mk
                                                  (limitedPrincipleOmniscienceDecodeBHist A)
                                                  (limitedPrincipleOmniscienceDecodeBHist S)
                                                  (limitedPrincipleOmniscienceDecodeBHist R)
                                                  (limitedPrincipleOmniscienceDecodeBHist D)
                                                  (limitedPrincipleOmniscienceDecodeBHist E)
                                                  (limitedPrincipleOmniscienceDecodeBHist T)
                                                  (limitedPrincipleOmniscienceDecodeBHist H)
                                                  (limitedPrincipleOmniscienceDecodeBHist C)
                                                  (limitedPrincipleOmniscienceDecodeBHist P)
                                                  (limitedPrincipleOmniscienceDecodeBHist N))
                                          | _ :: _ => none

private theorem limitedPrincipleOmniscience_round_trip :
    ∀ x : LimitedPrincipleOmniscienceUp,
      limitedPrincipleOmniscienceFromEventFlow
        (limitedPrincipleOmniscienceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A S R D E T H C P N =>
      change
        some
          (LimitedPrincipleOmniscienceUp.mk
            (limitedPrincipleOmniscienceDecodeBHist
              (limitedPrincipleOmniscienceEncodeBHist A))
            (limitedPrincipleOmniscienceDecodeBHist
              (limitedPrincipleOmniscienceEncodeBHist S))
            (limitedPrincipleOmniscienceDecodeBHist
              (limitedPrincipleOmniscienceEncodeBHist R))
            (limitedPrincipleOmniscienceDecodeBHist
              (limitedPrincipleOmniscienceEncodeBHist D))
            (limitedPrincipleOmniscienceDecodeBHist
              (limitedPrincipleOmniscienceEncodeBHist E))
            (limitedPrincipleOmniscienceDecodeBHist
              (limitedPrincipleOmniscienceEncodeBHist T))
            (limitedPrincipleOmniscienceDecodeBHist
              (limitedPrincipleOmniscienceEncodeBHist H))
            (limitedPrincipleOmniscienceDecodeBHist
              (limitedPrincipleOmniscienceEncodeBHist C))
            (limitedPrincipleOmniscienceDecodeBHist
              (limitedPrincipleOmniscienceEncodeBHist P))
            (limitedPrincipleOmniscienceDecodeBHist
              (limitedPrincipleOmniscienceEncodeBHist N))) =
          some (LimitedPrincipleOmniscienceUp.mk A S R D E T H C P N)
      rw [limitedPrincipleOmniscience_decode_encode_bhist A,
        limitedPrincipleOmniscience_decode_encode_bhist S,
        limitedPrincipleOmniscience_decode_encode_bhist R,
        limitedPrincipleOmniscience_decode_encode_bhist D,
        limitedPrincipleOmniscience_decode_encode_bhist E,
        limitedPrincipleOmniscience_decode_encode_bhist T,
        limitedPrincipleOmniscience_decode_encode_bhist H,
        limitedPrincipleOmniscience_decode_encode_bhist C,
        limitedPrincipleOmniscience_decode_encode_bhist P,
        limitedPrincipleOmniscience_decode_encode_bhist N]

private theorem limitedPrincipleOmniscienceToEventFlow_injective
    {x y : LimitedPrincipleOmniscienceUp} :
    limitedPrincipleOmniscienceToEventFlow x = limitedPrincipleOmniscienceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      limitedPrincipleOmniscienceFromEventFlow (limitedPrincipleOmniscienceToEventFlow x) =
        limitedPrincipleOmniscienceFromEventFlow (limitedPrincipleOmniscienceToEventFlow y) :=
    congrArg limitedPrincipleOmniscienceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (limitedPrincipleOmniscience_round_trip x).symm
      (Eq.trans hread (limitedPrincipleOmniscience_round_trip y)))

instance limitedPrincipleOmniscienceBHistCarrier :
    BHistCarrier LimitedPrincipleOmniscienceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := limitedPrincipleOmniscienceToEventFlow
  fromEventFlow := limitedPrincipleOmniscienceFromEventFlow

instance limitedPrincipleOmniscienceChapterTasteGate :
    ChapterTasteGate LimitedPrincipleOmniscienceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      limitedPrincipleOmniscienceFromEventFlow (limitedPrincipleOmniscienceToEventFlow x) =
        some x
    exact limitedPrincipleOmniscience_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (limitedPrincipleOmniscienceToEventFlow_injective heq)

theorem LimitedPrincipleOmniscienceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      limitedPrincipleOmniscienceDecodeBHist
        (limitedPrincipleOmniscienceEncodeBHist h) = h) ∧
      (∀ x : LimitedPrincipleOmniscienceUp,
        limitedPrincipleOmniscienceFromEventFlow
          (limitedPrincipleOmniscienceToEventFlow x) = some x) ∧
      (∀ x y : LimitedPrincipleOmniscienceUp,
        limitedPrincipleOmniscienceToEventFlow x =
          limitedPrincipleOmniscienceToEventFlow y → x = y) ∧
      limitedPrincipleOmniscienceEncodeBHist BHist.Empty = ([] : RawEvent) ∧
      (∃ x y : LimitedPrincipleOmniscienceUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact limitedPrincipleOmniscience_decode_encode_bhist
  constructor
  · exact limitedPrincipleOmniscience_round_trip
  constructor
  · intro x y heq
    exact limitedPrincipleOmniscienceToEventFlow_injective heq
  constructor
  · rfl
  · exact
      ⟨LimitedPrincipleOmniscienceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        LimitedPrincipleOmniscienceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty,
        by
          intro h
          cases h⟩

end BEDC.Derived.LimitedPrincipleOmniscienceUp
