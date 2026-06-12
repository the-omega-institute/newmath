import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BetaSubstitutionPreservationFrontierUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BetaSubstitutionPreservationFrontierUp : Type where
  | mk (B A R C L D H K P N : BHist) : BetaSubstitutionPreservationFrontierUp
  deriving DecidableEq

def betaSubstitutionPreservationFrontierFields :
    BetaSubstitutionPreservationFrontierUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BetaSubstitutionPreservationFrontierUp.mk B A R C L D H K P N =>
      [B, A, R, C, L, D, H, K, P, N]

def betaSubstitutionPreservationFrontierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: betaSubstitutionPreservationFrontierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: betaSubstitutionPreservationFrontierEncodeBHist h

def betaSubstitutionPreservationFrontierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (betaSubstitutionPreservationFrontierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (betaSubstitutionPreservationFrontierDecodeBHist tail)

private theorem betaSubstitutionPreservationFrontierDecode_encode_bhist :
    ∀ h : BHist,
      betaSubstitutionPreservationFrontierDecodeBHist
          (betaSubstitutionPreservationFrontierEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem betaSubstitutionPreservationFrontier_mk_congr
    {B B' A A' R R' C C' L L' D D' H H' K K' P P' N N' : BHist}
    (hB : B' = B) (hA : A' = A) (hR : R' = R) (hC : C' = C)
    (hL : L' = L) (hD : D' = D) (hH : H' = H) (hK : K' = K)
    (hP : P' = P) (hN : N' = N) :
    BetaSubstitutionPreservationFrontierUp.mk B' A' R' C' L' D' H' K' P' N' =
      BetaSubstitutionPreservationFrontierUp.mk B A R C L D H K P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hB
  cases hA
  cases hR
  cases hC
  cases hL
  cases hD
  cases hH
  cases hK
  cases hP
  cases hN
  rfl

def betaSubstitutionPreservationFrontierToEventFlow :
    BetaSubstitutionPreservationFrontierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BetaSubstitutionPreservationFrontierUp.mk B A R C L D H K P N =>
      [[BMark.b0],
        betaSubstitutionPreservationFrontierEncodeBHist B,
        [BMark.b1, BMark.b0],
        betaSubstitutionPreservationFrontierEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b0],
        betaSubstitutionPreservationFrontierEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        betaSubstitutionPreservationFrontierEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        betaSubstitutionPreservationFrontierEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        betaSubstitutionPreservationFrontierEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        betaSubstitutionPreservationFrontierEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        betaSubstitutionPreservationFrontierEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        betaSubstitutionPreservationFrontierEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        betaSubstitutionPreservationFrontierEncodeBHist N]

def betaSubstitutionPreservationFrontierFromEventFlow :
    EventFlow → Option BetaSubstitutionPreservationFrontierUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | B :: rest1 =>
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
                                      | L :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | D :: rest11 =>
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
                                                              | K :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | P :: rest17 =>
                                                                          match rest17
                                                                            with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match
                                                                                rest18
                                                                              with
                                                                              | [] =>
                                                                                  none
                                                                              | N ::
                                                                                  rest19 =>
                                                                                  match
                                                                                    rest19
                                                                                  with
                                                                                  | [] =>
                                                                                      some
                                                                                        (BetaSubstitutionPreservationFrontierUp.mk
                                                                                          (betaSubstitutionPreservationFrontierDecodeBHist
                                                                                            B)
                                                                                          (betaSubstitutionPreservationFrontierDecodeBHist
                                                                                            A)
                                                                                          (betaSubstitutionPreservationFrontierDecodeBHist
                                                                                            R)
                                                                                          (betaSubstitutionPreservationFrontierDecodeBHist
                                                                                            C)
                                                                                          (betaSubstitutionPreservationFrontierDecodeBHist
                                                                                            L)
                                                                                          (betaSubstitutionPreservationFrontierDecodeBHist
                                                                                            D)
                                                                                          (betaSubstitutionPreservationFrontierDecodeBHist
                                                                                            H)
                                                                                          (betaSubstitutionPreservationFrontierDecodeBHist
                                                                                            K)
                                                                                          (betaSubstitutionPreservationFrontierDecodeBHist
                                                                                            P)
                                                                                          (betaSubstitutionPreservationFrontierDecodeBHist
                                                                                            N))
                                                                                  | _ :: _ =>
                                                                                      none

private theorem betaSubstitutionPreservationFrontier_round_trip :
    ∀ x : BetaSubstitutionPreservationFrontierUp,
      betaSubstitutionPreservationFrontierFromEventFlow
          (betaSubstitutionPreservationFrontierToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B A R C L D H K P N =>
      change
        some
            (BetaSubstitutionPreservationFrontierUp.mk
              (betaSubstitutionPreservationFrontierDecodeBHist
                (betaSubstitutionPreservationFrontierEncodeBHist B))
              (betaSubstitutionPreservationFrontierDecodeBHist
                (betaSubstitutionPreservationFrontierEncodeBHist A))
              (betaSubstitutionPreservationFrontierDecodeBHist
                (betaSubstitutionPreservationFrontierEncodeBHist R))
              (betaSubstitutionPreservationFrontierDecodeBHist
                (betaSubstitutionPreservationFrontierEncodeBHist C))
              (betaSubstitutionPreservationFrontierDecodeBHist
                (betaSubstitutionPreservationFrontierEncodeBHist L))
              (betaSubstitutionPreservationFrontierDecodeBHist
                (betaSubstitutionPreservationFrontierEncodeBHist D))
              (betaSubstitutionPreservationFrontierDecodeBHist
                (betaSubstitutionPreservationFrontierEncodeBHist H))
              (betaSubstitutionPreservationFrontierDecodeBHist
                (betaSubstitutionPreservationFrontierEncodeBHist K))
              (betaSubstitutionPreservationFrontierDecodeBHist
                (betaSubstitutionPreservationFrontierEncodeBHist P))
              (betaSubstitutionPreservationFrontierDecodeBHist
                (betaSubstitutionPreservationFrontierEncodeBHist N))) =
          some (BetaSubstitutionPreservationFrontierUp.mk B A R C L D H K P N)
      exact
        congrArg some
          (betaSubstitutionPreservationFrontier_mk_congr
            (betaSubstitutionPreservationFrontierDecode_encode_bhist B)
            (betaSubstitutionPreservationFrontierDecode_encode_bhist A)
            (betaSubstitutionPreservationFrontierDecode_encode_bhist R)
            (betaSubstitutionPreservationFrontierDecode_encode_bhist C)
            (betaSubstitutionPreservationFrontierDecode_encode_bhist L)
            (betaSubstitutionPreservationFrontierDecode_encode_bhist D)
            (betaSubstitutionPreservationFrontierDecode_encode_bhist H)
            (betaSubstitutionPreservationFrontierDecode_encode_bhist K)
            (betaSubstitutionPreservationFrontierDecode_encode_bhist P)
            (betaSubstitutionPreservationFrontierDecode_encode_bhist N))

private theorem betaSubstitutionPreservationFrontierToEventFlow_injective
    {x y : BetaSubstitutionPreservationFrontierUp} :
    betaSubstitutionPreservationFrontierToEventFlow x =
        betaSubstitutionPreservationFrontierToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk B1 A1 R1 C1 L1 D1 H1 K1 P1 N1 =>
      cases y with
      | mk B2 A2 R2 C2 L2 D2 H2 K2 P2 N2 =>
          injection heq with _ hTail1
          injection hTail1 with hB hTail2
          injection hTail2 with _ hTail3
          injection hTail3 with hA hTail4
          injection hTail4 with _ hTail5
          injection hTail5 with hR hTail6
          injection hTail6 with _ hTail7
          injection hTail7 with hC hTail8
          injection hTail8 with _ hTail9
          injection hTail9 with hL hTail10
          injection hTail10 with _ hTail11
          injection hTail11 with hD hTail12
          injection hTail12 with _ hTail13
          injection hTail13 with hH hTail14
          injection hTail14 with _ hTail15
          injection hTail15 with hK hTail16
          injection hTail16 with _ hTail17
          injection hTail17 with hP hTail18
          injection hTail18 with _ hTail19
          injection hTail19 with hN _
          have hb : B1 = B2 := by
            exact Eq.trans (betaSubstitutionPreservationFrontierDecode_encode_bhist B1).symm
              (Eq.trans (congrArg betaSubstitutionPreservationFrontierDecodeBHist hB)
                (betaSubstitutionPreservationFrontierDecode_encode_bhist B2))
          have ha : A1 = A2 := by
            exact Eq.trans (betaSubstitutionPreservationFrontierDecode_encode_bhist A1).symm
              (Eq.trans (congrArg betaSubstitutionPreservationFrontierDecodeBHist hA)
                (betaSubstitutionPreservationFrontierDecode_encode_bhist A2))
          have hr : R1 = R2 := by
            exact Eq.trans (betaSubstitutionPreservationFrontierDecode_encode_bhist R1).symm
              (Eq.trans (congrArg betaSubstitutionPreservationFrontierDecodeBHist hR)
                (betaSubstitutionPreservationFrontierDecode_encode_bhist R2))
          have hc : C1 = C2 := by
            exact Eq.trans (betaSubstitutionPreservationFrontierDecode_encode_bhist C1).symm
              (Eq.trans (congrArg betaSubstitutionPreservationFrontierDecodeBHist hC)
                (betaSubstitutionPreservationFrontierDecode_encode_bhist C2))
          have hl : L1 = L2 := by
            exact Eq.trans (betaSubstitutionPreservationFrontierDecode_encode_bhist L1).symm
              (Eq.trans (congrArg betaSubstitutionPreservationFrontierDecodeBHist hL)
                (betaSubstitutionPreservationFrontierDecode_encode_bhist L2))
          have hd : D1 = D2 := by
            exact Eq.trans (betaSubstitutionPreservationFrontierDecode_encode_bhist D1).symm
              (Eq.trans (congrArg betaSubstitutionPreservationFrontierDecodeBHist hD)
                (betaSubstitutionPreservationFrontierDecode_encode_bhist D2))
          have hh : H1 = H2 := by
            exact Eq.trans (betaSubstitutionPreservationFrontierDecode_encode_bhist H1).symm
              (Eq.trans (congrArg betaSubstitutionPreservationFrontierDecodeBHist hH)
                (betaSubstitutionPreservationFrontierDecode_encode_bhist H2))
          have hk : K1 = K2 := by
            exact Eq.trans (betaSubstitutionPreservationFrontierDecode_encode_bhist K1).symm
              (Eq.trans (congrArg betaSubstitutionPreservationFrontierDecodeBHist hK)
                (betaSubstitutionPreservationFrontierDecode_encode_bhist K2))
          have hp : P1 = P2 := by
            exact Eq.trans (betaSubstitutionPreservationFrontierDecode_encode_bhist P1).symm
              (Eq.trans (congrArg betaSubstitutionPreservationFrontierDecodeBHist hP)
                (betaSubstitutionPreservationFrontierDecode_encode_bhist P2))
          have hn : N1 = N2 := by
            exact Eq.trans (betaSubstitutionPreservationFrontierDecode_encode_bhist N1).symm
              (Eq.trans (congrArg betaSubstitutionPreservationFrontierDecodeBHist hN)
                (betaSubstitutionPreservationFrontierDecode_encode_bhist N2))
          cases hb
          cases ha
          cases hr
          cases hc
          cases hl
          cases hd
          cases hh
          cases hk
          cases hp
          cases hn
          rfl

instance betaSubstitutionPreservationFrontierBHistCarrier :
    BHistCarrier BetaSubstitutionPreservationFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := betaSubstitutionPreservationFrontierToEventFlow
  fromEventFlow := betaSubstitutionPreservationFrontierFromEventFlow

instance betaSubstitutionPreservationFrontierChapterTasteGate :
    ChapterTasteGate BetaSubstitutionPreservationFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      betaSubstitutionPreservationFrontierFromEventFlow
          (betaSubstitutionPreservationFrontierToEventFlow x) =
        some x
    exact betaSubstitutionPreservationFrontier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (betaSubstitutionPreservationFrontierToEventFlow_injective heq)

instance betaSubstitutionPreservationFrontierFieldFaithful :
    FieldFaithful BetaSubstitutionPreservationFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := betaSubstitutionPreservationFrontierFields
  field_faithful := by
    intro x y h
    exact betaSubstitutionPreservationFrontierToEventFlow_injective (by
      cases x with
      | mk B1 A1 R1 C1 L1 D1 H1 K1 P1 N1 =>
          cases y with
          | mk B2 A2 R2 C2 L2 D2 H2 K2 P2 N2 =>
              simp only [betaSubstitutionPreservationFrontierFields] at h
              injection h with hB t1
              injection t1 with hA t2
              injection t2 with hR t3
              injection t3 with hC t4
              injection t4 with hL t5
              injection t5 with hD t6
              injection t6 with hH t7
              injection t7 with hK t8
              injection t8 with hP t9
              injection t9 with hN _
              cases hB
              cases hA
              cases hR
              cases hC
              cases hL
              cases hD
              cases hH
              cases hK
              cases hP
              cases hN
              rfl)

instance betaSubstitutionPreservationFrontierNontrivial :
    Nontrivial BetaSubstitutionPreservationFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BetaSubstitutionPreservationFrontierUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BetaSubstitutionPreservationFrontierUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem BetaSubstitutionPreservationFrontierTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      betaSubstitutionPreservationFrontierDecodeBHist
          (betaSubstitutionPreservationFrontierEncodeBHist h) =
        h) ∧
      (∀ x : BetaSubstitutionPreservationFrontierUp,
        betaSubstitutionPreservationFrontierFromEventFlow
            (betaSubstitutionPreservationFrontierToEventFlow x) =
          some x) ∧
        (∀ x y : BetaSubstitutionPreservationFrontierUp,
          betaSubstitutionPreservationFrontierToEventFlow x =
              betaSubstitutionPreservationFrontierToEventFlow y →
            x = y) ∧
          betaSubstitutionPreservationFrontierEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    And.intro betaSubstitutionPreservationFrontierDecode_encode_bhist
      (And.intro betaSubstitutionPreservationFrontier_round_trip
        (And.intro
          (fun x y heq => betaSubstitutionPreservationFrontierToEventFlow_injective heq)
          rfl))

end BEDC.Derived.BetaSubstitutionPreservationFrontierUp.TasteGate
