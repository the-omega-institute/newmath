import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DistanceToSetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DistanceToSetUp : Type where
  | mk (X A x r B R H C P N : BHist) : DistanceToSetUp
  deriving DecidableEq

def distanceToSetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: distanceToSetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: distanceToSetEncodeBHist h

def distanceToSetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (distanceToSetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (distanceToSetDecodeBHist tail)

private theorem DistanceToSetTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, distanceToSetDecodeBHist (distanceToSetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def DistanceToSetTasteGate_single_carrier_alignment_fields : DistanceToSetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DistanceToSetUp.mk X A x r B R H C P N => [X, A, x, r, B, R, H, C, P, N]

def distanceToSetToEventFlow : DistanceToSetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (DistanceToSetTasteGate_single_carrier_alignment_fields x).map distanceToSetEncodeBHist

def distanceToSetFromEventFlow : EventFlow → Option DistanceToSetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | X :: rest0 =>
      match rest0 with
      | [] => none
      | A :: rest1 =>
          match rest1 with
          | [] => none
          | x :: rest2 =>
              match rest2 with
              | [] => none
              | r :: rest3 =>
                  match rest3 with
                  | [] => none
                  | B :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
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
                                                (DistanceToSetUp.mk
                                                  (distanceToSetDecodeBHist X)
                                                  (distanceToSetDecodeBHist A)
                                                  (distanceToSetDecodeBHist x)
                                                  (distanceToSetDecodeBHist r)
                                                  (distanceToSetDecodeBHist B)
                                                  (distanceToSetDecodeBHist R)
                                                  (distanceToSetDecodeBHist H)
                                                  (distanceToSetDecodeBHist C)
                                                  (distanceToSetDecodeBHist P)
                                                  (distanceToSetDecodeBHist N))
                                          | _ :: _ => none

private theorem DistanceToSetTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DistanceToSetUp, distanceToSetFromEventFlow (distanceToSetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk X A x r B R H C P N =>
      change
        some
          (DistanceToSetUp.mk
            (distanceToSetDecodeBHist (distanceToSetEncodeBHist X))
            (distanceToSetDecodeBHist (distanceToSetEncodeBHist A))
            (distanceToSetDecodeBHist (distanceToSetEncodeBHist x))
            (distanceToSetDecodeBHist (distanceToSetEncodeBHist r))
            (distanceToSetDecodeBHist (distanceToSetEncodeBHist B))
            (distanceToSetDecodeBHist (distanceToSetEncodeBHist R))
            (distanceToSetDecodeBHist (distanceToSetEncodeBHist H))
            (distanceToSetDecodeBHist (distanceToSetEncodeBHist C))
            (distanceToSetDecodeBHist (distanceToSetEncodeBHist P))
            (distanceToSetDecodeBHist (distanceToSetEncodeBHist N))) =
          some (DistanceToSetUp.mk X A x r B R H C P N)
      rw [DistanceToSetTasteGate_single_carrier_alignment_decode_encode X,
        DistanceToSetTasteGate_single_carrier_alignment_decode_encode A,
        DistanceToSetTasteGate_single_carrier_alignment_decode_encode x,
        DistanceToSetTasteGate_single_carrier_alignment_decode_encode r,
        DistanceToSetTasteGate_single_carrier_alignment_decode_encode B,
        DistanceToSetTasteGate_single_carrier_alignment_decode_encode R,
        DistanceToSetTasteGate_single_carrier_alignment_decode_encode H,
        DistanceToSetTasteGate_single_carrier_alignment_decode_encode C,
        DistanceToSetTasteGate_single_carrier_alignment_decode_encode P,
        DistanceToSetTasteGate_single_carrier_alignment_decode_encode N]

theorem DistanceToSetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DistanceToSetUp} :
    distanceToSetToEventFlow x = distanceToSetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk X1 A1 x1 r1 B1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 A2 x2 r2 B2 R2 H2 C2 P2 N2 =>
          change
            [distanceToSetEncodeBHist X1, distanceToSetEncodeBHist A1,
              distanceToSetEncodeBHist x1, distanceToSetEncodeBHist r1,
              distanceToSetEncodeBHist B1, distanceToSetEncodeBHist R1,
              distanceToSetEncodeBHist H1, distanceToSetEncodeBHist C1,
              distanceToSetEncodeBHist P1, distanceToSetEncodeBHist N1] =
              [distanceToSetEncodeBHist X2, distanceToSetEncodeBHist A2,
                distanceToSetEncodeBHist x2, distanceToSetEncodeBHist r2,
                distanceToSetEncodeBHist B2, distanceToSetEncodeBHist R2,
                distanceToSetEncodeBHist H2, distanceToSetEncodeBHist C2,
                distanceToSetEncodeBHist P2, distanceToSetEncodeBHist N2] at heq
          injection heq with hX t1
          injection t1 with hA t2
          injection t2 with hx t3
          injection t3 with hr t4
          injection t4 with hB t5
          injection t5 with hR t6
          injection t6 with hH t7
          injection t7 with hC t8
          injection t8 with hP t9
          injection t9 with hN _
          have eX : X1 = X2 := by
            have h := congrArg distanceToSetDecodeBHist hX
            rw [DistanceToSetTasteGate_single_carrier_alignment_decode_encode X1,
              DistanceToSetTasteGate_single_carrier_alignment_decode_encode X2] at h
            exact h
          have eA : A1 = A2 := by
            have h := congrArg distanceToSetDecodeBHist hA
            rw [DistanceToSetTasteGate_single_carrier_alignment_decode_encode A1,
              DistanceToSetTasteGate_single_carrier_alignment_decode_encode A2] at h
            exact h
          have ex : x1 = x2 := by
            have h := congrArg distanceToSetDecodeBHist hx
            rw [DistanceToSetTasteGate_single_carrier_alignment_decode_encode x1,
              DistanceToSetTasteGate_single_carrier_alignment_decode_encode x2] at h
            exact h
          have er : r1 = r2 := by
            have h := congrArg distanceToSetDecodeBHist hr
            rw [DistanceToSetTasteGate_single_carrier_alignment_decode_encode r1,
              DistanceToSetTasteGate_single_carrier_alignment_decode_encode r2] at h
            exact h
          have eB : B1 = B2 := by
            have h := congrArg distanceToSetDecodeBHist hB
            rw [DistanceToSetTasteGate_single_carrier_alignment_decode_encode B1,
              DistanceToSetTasteGate_single_carrier_alignment_decode_encode B2] at h
            exact h
          have eR : R1 = R2 := by
            have h := congrArg distanceToSetDecodeBHist hR
            rw [DistanceToSetTasteGate_single_carrier_alignment_decode_encode R1,
              DistanceToSetTasteGate_single_carrier_alignment_decode_encode R2] at h
            exact h
          have eH : H1 = H2 := by
            have h := congrArg distanceToSetDecodeBHist hH
            rw [DistanceToSetTasteGate_single_carrier_alignment_decode_encode H1,
              DistanceToSetTasteGate_single_carrier_alignment_decode_encode H2] at h
            exact h
          have eC : C1 = C2 := by
            have h := congrArg distanceToSetDecodeBHist hC
            rw [DistanceToSetTasteGate_single_carrier_alignment_decode_encode C1,
              DistanceToSetTasteGate_single_carrier_alignment_decode_encode C2] at h
            exact h
          have eP : P1 = P2 := by
            have h := congrArg distanceToSetDecodeBHist hP
            rw [DistanceToSetTasteGate_single_carrier_alignment_decode_encode P1,
              DistanceToSetTasteGate_single_carrier_alignment_decode_encode P2] at h
            exact h
          have eN : N1 = N2 := by
            have h := congrArg distanceToSetDecodeBHist hN
            rw [DistanceToSetTasteGate_single_carrier_alignment_decode_encode N1,
              DistanceToSetTasteGate_single_carrier_alignment_decode_encode N2] at h
            exact h
          subst eX
          subst eA
          subst ex
          subst er
          subst eB
          subst eR
          subst eH
          subst eC
          subst eP
          subst eN
          rfl

private theorem DistanceToSetTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : DistanceToSetUp,
      DistanceToSetTasteGate_single_carrier_alignment_fields x =
        DistanceToSetTasteGate_single_carrier_alignment_fields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 A1 x1 r1 B1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 A2 x2 r2 B2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance distanceToSetBHistCarrier : BHistCarrier DistanceToSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := distanceToSetToEventFlow
  fromEventFlow := distanceToSetFromEventFlow

instance distanceToSetChapterTasteGate : ChapterTasteGate DistanceToSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change distanceToSetFromEventFlow (distanceToSetToEventFlow x) = some x
    exact DistanceToSetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DistanceToSetTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance distanceToSetFieldFaithful : FieldFaithful DistanceToSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := DistanceToSetTasteGate_single_carrier_alignment_fields
  field_faithful := DistanceToSetTasteGate_single_carrier_alignment_fields_faithful

instance distanceToSetNontrivial : Nontrivial DistanceToSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DistanceToSetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DistanceToSetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem DistanceToSetTasteGate_single_carrier_alignment :
    (∀ h : BHist, distanceToSetDecodeBHist (distanceToSetEncodeBHist h) = h) ∧
      (∀ x : DistanceToSetUp, distanceToSetFromEventFlow (distanceToSetToEventFlow x) = some x) ∧
      (∀ x y : DistanceToSetUp,
        distanceToSetToEventFlow x = distanceToSetToEventFlow y → x = y) ∧
      distanceToSetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  · constructor
    · intro token
      cases token with
      | mk X A x r B R H C P N =>
          change
            some
              (DistanceToSetUp.mk
                (distanceToSetDecodeBHist (distanceToSetEncodeBHist X))
                (distanceToSetDecodeBHist (distanceToSetEncodeBHist A))
                (distanceToSetDecodeBHist (distanceToSetEncodeBHist x))
                (distanceToSetDecodeBHist (distanceToSetEncodeBHist r))
                (distanceToSetDecodeBHist (distanceToSetEncodeBHist B))
                (distanceToSetDecodeBHist (distanceToSetEncodeBHist R))
                (distanceToSetDecodeBHist (distanceToSetEncodeBHist H))
                (distanceToSetDecodeBHist (distanceToSetEncodeBHist C))
                (distanceToSetDecodeBHist (distanceToSetEncodeBHist P))
                (distanceToSetDecodeBHist (distanceToSetEncodeBHist N))) =
              some (DistanceToSetUp.mk X A x r B R H C P N)
          have eX : distanceToSetDecodeBHist (distanceToSetEncodeBHist X) = X := by
            induction X with
            | Empty => rfl
            | e0 X ih => exact congrArg BHist.e0 ih
            | e1 X ih => exact congrArg BHist.e1 ih
          have eA : distanceToSetDecodeBHist (distanceToSetEncodeBHist A) = A := by
            induction A with
            | Empty => rfl
            | e0 A ih => exact congrArg BHist.e0 ih
            | e1 A ih => exact congrArg BHist.e1 ih
          have ex : distanceToSetDecodeBHist (distanceToSetEncodeBHist x) = x := by
            induction x with
            | Empty => rfl
            | e0 x ih => exact congrArg BHist.e0 ih
            | e1 x ih => exact congrArg BHist.e1 ih
          have er : distanceToSetDecodeBHist (distanceToSetEncodeBHist r) = r := by
            induction r with
            | Empty => rfl
            | e0 r ih => exact congrArg BHist.e0 ih
            | e1 r ih => exact congrArg BHist.e1 ih
          have eB : distanceToSetDecodeBHist (distanceToSetEncodeBHist B) = B := by
            induction B with
            | Empty => rfl
            | e0 B ih => exact congrArg BHist.e0 ih
            | e1 B ih => exact congrArg BHist.e1 ih
          have eR : distanceToSetDecodeBHist (distanceToSetEncodeBHist R) = R := by
            induction R with
            | Empty => rfl
            | e0 R ih => exact congrArg BHist.e0 ih
            | e1 R ih => exact congrArg BHist.e1 ih
          have eH : distanceToSetDecodeBHist (distanceToSetEncodeBHist H) = H := by
            induction H with
            | Empty => rfl
            | e0 H ih => exact congrArg BHist.e0 ih
            | e1 H ih => exact congrArg BHist.e1 ih
          have eC : distanceToSetDecodeBHist (distanceToSetEncodeBHist C) = C := by
            induction C with
            | Empty => rfl
            | e0 C ih => exact congrArg BHist.e0 ih
            | e1 C ih => exact congrArg BHist.e1 ih
          have eP : distanceToSetDecodeBHist (distanceToSetEncodeBHist P) = P := by
            induction P with
            | Empty => rfl
            | e0 P ih => exact congrArg BHist.e0 ih
            | e1 P ih => exact congrArg BHist.e1 ih
          have eN : distanceToSetDecodeBHist (distanceToSetEncodeBHist N) = N := by
            induction N with
            | Empty => rfl
            | e0 N ih => exact congrArg BHist.e0 ih
            | e1 N ih => exact congrArg BHist.e1 ih
          rw [eX, eA, ex, er, eB, eR, eH, eC, eP, eN]
    · constructor
      · intro x y heq
        exact DistanceToSetTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.DistanceToSetUp
