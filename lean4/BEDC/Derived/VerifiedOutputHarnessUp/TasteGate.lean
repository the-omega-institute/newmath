import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.VerifiedOutputHarnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive VerifiedOutputHarnessUp : Type where
  | mk : (I T M Q O C A R H K P N : BHist) → VerifiedOutputHarnessUp
  deriving DecidableEq

def verifiedOutputHarnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: verifiedOutputHarnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: verifiedOutputHarnessEncodeBHist h

def verifiedOutputHarnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (verifiedOutputHarnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (verifiedOutputHarnessDecodeBHist tail)

private theorem verifiedOutputHarness_decode_encode_bhist :
    ∀ h : BHist,
      verifiedOutputHarnessDecodeBHist (verifiedOutputHarnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def verifiedOutputHarnessToEventFlow : VerifiedOutputHarnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | VerifiedOutputHarnessUp.mk I T M Q O C A R H K P N =>
      [[BMark.b0],
        verifiedOutputHarnessEncodeBHist I,
        [BMark.b1, BMark.b0],
        verifiedOutputHarnessEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b0],
        verifiedOutputHarnessEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        verifiedOutputHarnessEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        verifiedOutputHarnessEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        verifiedOutputHarnessEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        verifiedOutputHarnessEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        verifiedOutputHarnessEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        verifiedOutputHarnessEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        verifiedOutputHarnessEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        verifiedOutputHarnessEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        verifiedOutputHarnessEncodeBHist N]

def verifiedOutputHarnessFromEventFlow : EventFlow → Option VerifiedOutputHarnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | I :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | T :: rest3 =>
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
                              | Q :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | O :: rest9 =>
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
                                                      | A :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | R :: rest15 =>
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
                                                                              | K :: rest19 =>
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
                                                                                                        (VerifiedOutputHarnessUp.mk
                                                                                                          (verifiedOutputHarnessDecodeBHist I)
                                                                                                          (verifiedOutputHarnessDecodeBHist T)
                                                                                                          (verifiedOutputHarnessDecodeBHist M)
                                                                                                          (verifiedOutputHarnessDecodeBHist Q)
                                                                                                          (verifiedOutputHarnessDecodeBHist O)
                                                                                                          (verifiedOutputHarnessDecodeBHist C)
                                                                                                          (verifiedOutputHarnessDecodeBHist A)
                                                                                                          (verifiedOutputHarnessDecodeBHist R)
                                                                                                          (verifiedOutputHarnessDecodeBHist H)
                                                                                                          (verifiedOutputHarnessDecodeBHist K)
                                                                                                          (verifiedOutputHarnessDecodeBHist P)
                                                                                                          (verifiedOutputHarnessDecodeBHist N))
                                                                                                  | _ :: _ => none

private theorem verifiedOutputHarness_round_trip :
    ∀ x : VerifiedOutputHarnessUp,
      verifiedOutputHarnessFromEventFlow (verifiedOutputHarnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I T M Q O C A R H K P N =>
      change
        some
          (VerifiedOutputHarnessUp.mk
            (verifiedOutputHarnessDecodeBHist (verifiedOutputHarnessEncodeBHist I))
            (verifiedOutputHarnessDecodeBHist (verifiedOutputHarnessEncodeBHist T))
            (verifiedOutputHarnessDecodeBHist (verifiedOutputHarnessEncodeBHist M))
            (verifiedOutputHarnessDecodeBHist (verifiedOutputHarnessEncodeBHist Q))
            (verifiedOutputHarnessDecodeBHist (verifiedOutputHarnessEncodeBHist O))
            (verifiedOutputHarnessDecodeBHist (verifiedOutputHarnessEncodeBHist C))
            (verifiedOutputHarnessDecodeBHist (verifiedOutputHarnessEncodeBHist A))
            (verifiedOutputHarnessDecodeBHist (verifiedOutputHarnessEncodeBHist R))
            (verifiedOutputHarnessDecodeBHist (verifiedOutputHarnessEncodeBHist H))
            (verifiedOutputHarnessDecodeBHist (verifiedOutputHarnessEncodeBHist K))
            (verifiedOutputHarnessDecodeBHist (verifiedOutputHarnessEncodeBHist P))
            (verifiedOutputHarnessDecodeBHist (verifiedOutputHarnessEncodeBHist N))) =
          some (VerifiedOutputHarnessUp.mk I T M Q O C A R H K P N)
      rw [verifiedOutputHarness_decode_encode_bhist I,
        verifiedOutputHarness_decode_encode_bhist T,
        verifiedOutputHarness_decode_encode_bhist M,
        verifiedOutputHarness_decode_encode_bhist Q,
        verifiedOutputHarness_decode_encode_bhist O,
        verifiedOutputHarness_decode_encode_bhist C,
        verifiedOutputHarness_decode_encode_bhist A,
        verifiedOutputHarness_decode_encode_bhist R,
        verifiedOutputHarness_decode_encode_bhist H,
        verifiedOutputHarness_decode_encode_bhist K,
        verifiedOutputHarness_decode_encode_bhist P,
        verifiedOutputHarness_decode_encode_bhist N]

private theorem verifiedOutputHarnessToEventFlow_injective
    {x y : VerifiedOutputHarnessUp} :
    verifiedOutputHarnessToEventFlow x = verifiedOutputHarnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      verifiedOutputHarnessFromEventFlow (verifiedOutputHarnessToEventFlow x) =
        verifiedOutputHarnessFromEventFlow (verifiedOutputHarnessToEventFlow y) :=
    congrArg verifiedOutputHarnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (verifiedOutputHarness_round_trip x).symm
      (Eq.trans hread (verifiedOutputHarness_round_trip y)))

instance verifiedOutputHarnessBHistCarrier : BHistCarrier VerifiedOutputHarnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := verifiedOutputHarnessToEventFlow
  fromEventFlow := verifiedOutputHarnessFromEventFlow

instance verifiedOutputHarnessChapterTasteGate :
    ChapterTasteGate VerifiedOutputHarnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change verifiedOutputHarnessFromEventFlow (verifiedOutputHarnessToEventFlow x) = some x
    exact verifiedOutputHarness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (verifiedOutputHarnessToEventFlow_injective heq)

instance verifiedOutputHarnessFieldFaithful : FieldFaithful VerifiedOutputHarnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | VerifiedOutputHarnessUp.mk I T M Q O C A R H K P N =>
        [I, T, M, Q, O, C, A, R, H, K, P, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk I1 T1 M1 Q1 O1 C1 A1 R1 H1 K1 P1 N1 =>
        cases y with
        | mk I2 T2 M2 Q2 O2 C2 A2 R2 H2 K2 P2 N2 =>
            injection h with hI t1
            injection t1 with hT t2
            injection t2 with hM t3
            injection t3 with hQ t4
            injection t4 with hO t5
            injection t5 with hC t6
            injection t6 with hA t7
            injection t7 with hR t8
            injection t8 with hH t9
            injection t9 with hK t10
            injection t10 with hP t11
            injection t11 with hN _
            cases hI
            cases hT
            cases hM
            cases hQ
            cases hO
            cases hC
            cases hA
            cases hR
            cases hH
            cases hK
            cases hP
            cases hN
            rfl

theorem VerifiedOutputHarnessTasteGate_single_carrier_alignment :
    (∀ h : BHist, verifiedOutputHarnessDecodeBHist (verifiedOutputHarnessEncodeBHist h) = h) ∧
      (∀ x : VerifiedOutputHarnessUp,
        verifiedOutputHarnessFromEventFlow (verifiedOutputHarnessToEventFlow x) = some x) ∧
        (∀ x y : VerifiedOutputHarnessUp,
          verifiedOutputHarnessToEventFlow x = verifiedOutputHarnessToEventFlow y → x = y) ∧
          verifiedOutputHarnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact verifiedOutputHarness_decode_encode_bhist
  · constructor
    · exact verifiedOutputHarness_round_trip
    · constructor
      · intro x y heq
        exact verifiedOutputHarnessToEventFlow_injective heq
      · rfl

end BEDC.Derived.VerifiedOutputHarnessUp
