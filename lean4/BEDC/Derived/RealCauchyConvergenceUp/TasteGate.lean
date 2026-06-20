import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCauchyConvergenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealCauchyConvergenceUp : Type where
  | mk : (D S R T B E H C P N : BHist) → RealCauchyConvergenceUp
  deriving DecidableEq

def realCauchyConvergenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCauchyConvergenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCauchyConvergenceEncodeBHist h

def realCauchyConvergenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCauchyConvergenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCauchyConvergenceDecodeBHist tail)

private theorem realCauchyConvergence_decode_encode :
    ∀ h : BHist,
      realCauchyConvergenceDecodeBHist (realCauchyConvergenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realCauchyConvergenceFields : RealCauchyConvergenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealCauchyConvergenceUp.mk D S R T B E H C P N => [D, S, R, T, B, E, H, C, P, N]

def realCauchyConvergenceToEventFlow : RealCauchyConvergenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realCauchyConvergenceFields x).map realCauchyConvergenceEncodeBHist

def realCauchyConvergenceFromEventFlow : EventFlow → Option RealCauchyConvergenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | D :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | R :: rest2 =>
              match rest2 with
              | [] => none
              | T :: rest3 =>
                  match rest3 with
                  | [] => none
                  | B :: rest4 =>
                      match rest4 with
                      | [] => none
                      | E :: rest5 =>
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
                                                (RealCauchyConvergenceUp.mk
                                                  (realCauchyConvergenceDecodeBHist D)
                                                  (realCauchyConvergenceDecodeBHist S)
                                                  (realCauchyConvergenceDecodeBHist R)
                                                  (realCauchyConvergenceDecodeBHist T)
                                                  (realCauchyConvergenceDecodeBHist B)
                                                  (realCauchyConvergenceDecodeBHist E)
                                                  (realCauchyConvergenceDecodeBHist H)
                                                  (realCauchyConvergenceDecodeBHist C)
                                                  (realCauchyConvergenceDecodeBHist P)
                                                  (realCauchyConvergenceDecodeBHist N))
                                          | _ :: _ => none

private theorem realCauchyConvergence_round_trip :
    ∀ x : RealCauchyConvergenceUp,
      realCauchyConvergenceFromEventFlow (realCauchyConvergenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R T B E H C P N =>
      change
        some
          (RealCauchyConvergenceUp.mk
            (realCauchyConvergenceDecodeBHist (realCauchyConvergenceEncodeBHist D))
            (realCauchyConvergenceDecodeBHist (realCauchyConvergenceEncodeBHist S))
            (realCauchyConvergenceDecodeBHist (realCauchyConvergenceEncodeBHist R))
            (realCauchyConvergenceDecodeBHist (realCauchyConvergenceEncodeBHist T))
            (realCauchyConvergenceDecodeBHist (realCauchyConvergenceEncodeBHist B))
            (realCauchyConvergenceDecodeBHist (realCauchyConvergenceEncodeBHist E))
            (realCauchyConvergenceDecodeBHist (realCauchyConvergenceEncodeBHist H))
            (realCauchyConvergenceDecodeBHist (realCauchyConvergenceEncodeBHist C))
            (realCauchyConvergenceDecodeBHist (realCauchyConvergenceEncodeBHist P))
            (realCauchyConvergenceDecodeBHist (realCauchyConvergenceEncodeBHist N))) =
          some (RealCauchyConvergenceUp.mk D S R T B E H C P N)
      rw [realCauchyConvergence_decode_encode D, realCauchyConvergence_decode_encode S,
        realCauchyConvergence_decode_encode R, realCauchyConvergence_decode_encode T,
        realCauchyConvergence_decode_encode B, realCauchyConvergence_decode_encode E,
        realCauchyConvergence_decode_encode H, realCauchyConvergence_decode_encode C,
        realCauchyConvergence_decode_encode P, realCauchyConvergence_decode_encode N]

private theorem realCauchyConvergenceToEventFlow_injective
    {x y : RealCauchyConvergenceUp} :
    realCauchyConvergenceToEventFlow x = realCauchyConvergenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCauchyConvergenceFromEventFlow (realCauchyConvergenceToEventFlow x) =
        realCauchyConvergenceFromEventFlow (realCauchyConvergenceToEventFlow y) :=
    congrArg realCauchyConvergenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realCauchyConvergence_round_trip x).symm
      (Eq.trans hread (realCauchyConvergence_round_trip y)))

private theorem realCauchyConvergence_fields_faithful :
    ∀ x y : RealCauchyConvergenceUp,
      realCauchyConvergenceFields x = realCauchyConvergenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk D1 S1 R1 T1 B1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk D2 S2 R2 T2 B2 E2 H2 C2 P2 N2 =>
          injection h with hD t1
          injection t1 with hS t2
          injection t2 with hR t3
          injection t3 with hT t4
          injection t4 with hB t5
          injection t5 with hE t6
          injection t6 with hH t7
          injection t7 with hC t8
          injection t8 with hP t9
          injection t9 with hN _
          subst hD
          subst hS
          subst hR
          subst hT
          subst hB
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance realCauchyConvergenceBHistCarrier : BHistCarrier RealCauchyConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCauchyConvergenceToEventFlow
  fromEventFlow := realCauchyConvergenceFromEventFlow

instance realCauchyConvergenceChapterTasteGate : ChapterTasteGate RealCauchyConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realCauchyConvergenceFromEventFlow (realCauchyConvergenceToEventFlow x) = some x
    exact realCauchyConvergence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realCauchyConvergenceToEventFlow_injective heq)

instance realCauchyConvergenceFieldFaithful : FieldFaithful RealCauchyConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realCauchyConvergenceFields
  field_faithful := realCauchyConvergence_fields_faithful

instance realCauchyConvergenceNontrivial : Nontrivial RealCauchyConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealCauchyConvergenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealCauchyConvergenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealCauchyConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realCauchyConvergenceChapterTasteGate

theorem RealCauchyConvergenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realCauchyConvergenceDecodeBHist (realCauchyConvergenceEncodeBHist h) = h) ∧
      (∀ x : RealCauchyConvergenceUp,
        realCauchyConvergenceFromEventFlow (realCauchyConvergenceToEventFlow x) = some x) ∧
      (∀ x y : RealCauchyConvergenceUp,
        realCauchyConvergenceToEventFlow x = realCauchyConvergenceToEventFlow y → x = y) ∧
      realCauchyConvergenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  let decodeEncode :
      ∀ h : BHist,
        realCauchyConvergenceDecodeBHist (realCauchyConvergenceEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  let roundTrip :
      ∀ x : RealCauchyConvergenceUp,
        realCauchyConvergenceFromEventFlow (realCauchyConvergenceToEventFlow x) = some x := by
    intro x
    cases x with
    | mk D S R T B E H C P N =>
        change
          some
            (RealCauchyConvergenceUp.mk
              (realCauchyConvergenceDecodeBHist (realCauchyConvergenceEncodeBHist D))
              (realCauchyConvergenceDecodeBHist (realCauchyConvergenceEncodeBHist S))
              (realCauchyConvergenceDecodeBHist (realCauchyConvergenceEncodeBHist R))
              (realCauchyConvergenceDecodeBHist (realCauchyConvergenceEncodeBHist T))
              (realCauchyConvergenceDecodeBHist (realCauchyConvergenceEncodeBHist B))
              (realCauchyConvergenceDecodeBHist (realCauchyConvergenceEncodeBHist E))
              (realCauchyConvergenceDecodeBHist (realCauchyConvergenceEncodeBHist H))
              (realCauchyConvergenceDecodeBHist (realCauchyConvergenceEncodeBHist C))
              (realCauchyConvergenceDecodeBHist (realCauchyConvergenceEncodeBHist P))
              (realCauchyConvergenceDecodeBHist (realCauchyConvergenceEncodeBHist N))) =
            some (RealCauchyConvergenceUp.mk D S R T B E H C P N)
        let mkCongr
            {D' S' R' T' B' E' H' C' P' N' : BHist}
            (hD : D' = D)
            (hS : S' = S)
            (hR : R' = R)
            (hT : T' = T)
            (hB : B' = B)
            (hE : E' = E)
            (hH : H' = H)
            (hC : C' = C)
            (hP : P' = P)
            (hN : N' = N) :
            RealCauchyConvergenceUp.mk D' S' R' T' B' E' H' C' P' N' =
              RealCauchyConvergenceUp.mk D S R T B E H C P N := by
          cases hD
          cases hS
          cases hR
          cases hT
          cases hB
          cases hE
          cases hH
          cases hC
          cases hP
          cases hN
          rfl
        exact
          congrArg some
            (mkCongr (decodeEncode D) (decodeEncode S) (decodeEncode R)
              (decodeEncode T) (decodeEncode B) (decodeEncode E) (decodeEncode H)
              (decodeEncode C) (decodeEncode P) (decodeEncode N))
  let toEventFlowInjective :
      ∀ x y : RealCauchyConvergenceUp,
        realCauchyConvergenceToEventFlow x = realCauchyConvergenceToEventFlow y → x = y := by
    intro x y heq
    have hread :
        realCauchyConvergenceFromEventFlow (realCauchyConvergenceToEventFlow x) =
          realCauchyConvergenceFromEventFlow (realCauchyConvergenceToEventFlow y) :=
      congrArg realCauchyConvergenceFromEventFlow heq
    exact Option.some.inj (Eq.trans (roundTrip x).symm (Eq.trans hread (roundTrip y)))
  exact
    ⟨decodeEncode, roundTrip, fun x y heq => toEventFlowInjective x y heq, rfl⟩

end BEDC.Derived.RealCauchyConvergenceUp
