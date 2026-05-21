import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyInterleavingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyInterleavingUp : Type where
  | mk :
      (A B SA SB sigma M EA EB E H C P N : BHist) →
        RegularCauchyInterleavingUp
  deriving DecidableEq

def RegularCauchyInterleavingTasteGate_single_carrier_alignment_fields :
    RegularCauchyInterleavingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyInterleavingUp.mk A B SA SB sigma M EA EB E H C P N =>
      [A, B, SA, SB, sigma, M, EA, EB, E, H, C, P, N]

def RegularCauchyInterleavingTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 ::
        RegularCauchyInterleavingTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 ::
        RegularCauchyInterleavingTasteGate_single_carrier_alignment_encodeBHist h

def RegularCauchyInterleavingTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (RegularCauchyInterleavingTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (RegularCauchyInterleavingTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem RegularCauchyInterleavingTasteGate_single_carrier_alignment_decode_encode_bhist :
    ∀ h : BHist,
      RegularCauchyInterleavingTasteGate_single_carrier_alignment_decodeBHist
        (RegularCauchyInterleavingTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def RegularCauchyInterleavingTasteGate_single_carrier_alignment_toEventFlow :
    RegularCauchyInterleavingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyInterleavingUp.mk A B SA SB sigma M EA EB E H C P N =>
      [[BMark.b0],
        RegularCauchyInterleavingTasteGate_single_carrier_alignment_encodeBHist A,
        [BMark.b1, BMark.b0],
        RegularCauchyInterleavingTasteGate_single_carrier_alignment_encodeBHist B,
        [BMark.b1, BMark.b1, BMark.b0],
        RegularCauchyInterleavingTasteGate_single_carrier_alignment_encodeBHist SA,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        RegularCauchyInterleavingTasteGate_single_carrier_alignment_encodeBHist SB,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        RegularCauchyInterleavingTasteGate_single_carrier_alignment_encodeBHist sigma,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        RegularCauchyInterleavingTasteGate_single_carrier_alignment_encodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        RegularCauchyInterleavingTasteGate_single_carrier_alignment_encodeBHist EA,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        RegularCauchyInterleavingTasteGate_single_carrier_alignment_encodeBHist EB,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        RegularCauchyInterleavingTasteGate_single_carrier_alignment_encodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        RegularCauchyInterleavingTasteGate_single_carrier_alignment_encodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        RegularCauchyInterleavingTasteGate_single_carrier_alignment_encodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        RegularCauchyInterleavingTasteGate_single_carrier_alignment_encodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        RegularCauchyInterleavingTasteGate_single_carrier_alignment_encodeBHist N]

def RegularCauchyInterleavingTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option RegularCauchyInterleavingUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | A :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | B :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | SA :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | SB :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | sigma :: rest9 =>
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
                                                      | EA :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | EB :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | E :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match
                                                                                rest18
                                                                              with
                                                                              | [] =>
                                                                                  none
                                                                              | H ::
                                                                                  rest19 =>
                                                                                  match
                                                                                    rest19
                                                                                  with
                                                                                  | [] =>
                                                                                      none
                                                                                  | _tag10 ::
                                                                                      rest20 =>
                                                                                      match
                                                                                        rest20
                                                                                      with
                                                                                      | [] =>
                                                                                          none
                                                                                      | C ::
                                                                                          rest21 =>
                                                                                          match
                                                                                            rest21
                                                                                          with
                                                                                          | [] =>
                                                                                              none
                                                                                          | _tag11 ::
                                                                                              rest22 =>
                                                                                              match
                                                                                                rest22
                                                                                              with
                                                                                              | [] =>
                                                                                                  none
                                                                                              | P ::
                                                                                                  rest23 =>
                                                                                                  match
                                                                                                    rest23
                                                                                                  with
                                                                                                  | [] =>
                                                                                                      none
                                                                                                  | _tag12 ::
                                                                                                      rest24 =>
                                                                                                      match
                                                                                                        rest24
                                                                                                      with
                                                                                                      | [] =>
                                                                                                          none
                                                                                                      | N ::
                                                                                                          rest25 =>
                                                                                                          match
                                                                                                            rest25
                                                                                                          with
                                                                                                          | [] =>
                                                                                                              some
                                                                                                                (RegularCauchyInterleavingUp.mk
                                                                                                                  (RegularCauchyInterleavingTasteGate_single_carrier_alignment_decodeBHist
                                                                                                                    A)
                                                                                                                  (RegularCauchyInterleavingTasteGate_single_carrier_alignment_decodeBHist
                                                                                                                    B)
                                                                                                                  (RegularCauchyInterleavingTasteGate_single_carrier_alignment_decodeBHist
                                                                                                                    SA)
                                                                                                                  (RegularCauchyInterleavingTasteGate_single_carrier_alignment_decodeBHist
                                                                                                                    SB)
                                                                                                                  (RegularCauchyInterleavingTasteGate_single_carrier_alignment_decodeBHist
                                                                                                                    sigma)
                                                                                                                  (RegularCauchyInterleavingTasteGate_single_carrier_alignment_decodeBHist
                                                                                                                    M)
                                                                                                                  (RegularCauchyInterleavingTasteGate_single_carrier_alignment_decodeBHist
                                                                                                                    EA)
                                                                                                                  (RegularCauchyInterleavingTasteGate_single_carrier_alignment_decodeBHist
                                                                                                                    EB)
                                                                                                                  (RegularCauchyInterleavingTasteGate_single_carrier_alignment_decodeBHist
                                                                                                                    E)
                                                                                                                  (RegularCauchyInterleavingTasteGate_single_carrier_alignment_decodeBHist
                                                                                                                    H)
                                                                                                                  (RegularCauchyInterleavingTasteGate_single_carrier_alignment_decodeBHist
                                                                                                                    C)
                                                                                                                  (RegularCauchyInterleavingTasteGate_single_carrier_alignment_decodeBHist
                                                                                                                    P)
                                                                                                                  (RegularCauchyInterleavingTasteGate_single_carrier_alignment_decodeBHist
                                                                                                                    N))
                                                                                                          | _ ::
                                                                                                              _ =>
                                                                                                              none

private theorem RegularCauchyInterleavingTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyInterleavingUp,
      RegularCauchyInterleavingTasteGate_single_carrier_alignment_fromEventFlow
        (RegularCauchyInterleavingTasteGate_single_carrier_alignment_toEventFlow x) =
          some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B SA SB sigma M EA EB E H C P N =>
      change
        some
          (RegularCauchyInterleavingUp.mk
            (RegularCauchyInterleavingTasteGate_single_carrier_alignment_decodeBHist
              (RegularCauchyInterleavingTasteGate_single_carrier_alignment_encodeBHist A))
            (RegularCauchyInterleavingTasteGate_single_carrier_alignment_decodeBHist
              (RegularCauchyInterleavingTasteGate_single_carrier_alignment_encodeBHist B))
            (RegularCauchyInterleavingTasteGate_single_carrier_alignment_decodeBHist
              (RegularCauchyInterleavingTasteGate_single_carrier_alignment_encodeBHist SA))
            (RegularCauchyInterleavingTasteGate_single_carrier_alignment_decodeBHist
              (RegularCauchyInterleavingTasteGate_single_carrier_alignment_encodeBHist SB))
            (RegularCauchyInterleavingTasteGate_single_carrier_alignment_decodeBHist
              (RegularCauchyInterleavingTasteGate_single_carrier_alignment_encodeBHist sigma))
            (RegularCauchyInterleavingTasteGate_single_carrier_alignment_decodeBHist
              (RegularCauchyInterleavingTasteGate_single_carrier_alignment_encodeBHist M))
            (RegularCauchyInterleavingTasteGate_single_carrier_alignment_decodeBHist
              (RegularCauchyInterleavingTasteGate_single_carrier_alignment_encodeBHist EA))
            (RegularCauchyInterleavingTasteGate_single_carrier_alignment_decodeBHist
              (RegularCauchyInterleavingTasteGate_single_carrier_alignment_encodeBHist EB))
            (RegularCauchyInterleavingTasteGate_single_carrier_alignment_decodeBHist
              (RegularCauchyInterleavingTasteGate_single_carrier_alignment_encodeBHist E))
            (RegularCauchyInterleavingTasteGate_single_carrier_alignment_decodeBHist
              (RegularCauchyInterleavingTasteGate_single_carrier_alignment_encodeBHist H))
            (RegularCauchyInterleavingTasteGate_single_carrier_alignment_decodeBHist
              (RegularCauchyInterleavingTasteGate_single_carrier_alignment_encodeBHist C))
            (RegularCauchyInterleavingTasteGate_single_carrier_alignment_decodeBHist
              (RegularCauchyInterleavingTasteGate_single_carrier_alignment_encodeBHist P))
            (RegularCauchyInterleavingTasteGate_single_carrier_alignment_decodeBHist
              (RegularCauchyInterleavingTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (RegularCauchyInterleavingUp.mk A B SA SB sigma M EA EB E H C P N)
      rw [RegularCauchyInterleavingTasteGate_single_carrier_alignment_decode_encode_bhist A,
        RegularCauchyInterleavingTasteGate_single_carrier_alignment_decode_encode_bhist B,
        RegularCauchyInterleavingTasteGate_single_carrier_alignment_decode_encode_bhist SA,
        RegularCauchyInterleavingTasteGate_single_carrier_alignment_decode_encode_bhist SB,
        RegularCauchyInterleavingTasteGate_single_carrier_alignment_decode_encode_bhist sigma,
        RegularCauchyInterleavingTasteGate_single_carrier_alignment_decode_encode_bhist M,
        RegularCauchyInterleavingTasteGate_single_carrier_alignment_decode_encode_bhist EA,
        RegularCauchyInterleavingTasteGate_single_carrier_alignment_decode_encode_bhist EB,
        RegularCauchyInterleavingTasteGate_single_carrier_alignment_decode_encode_bhist E,
        RegularCauchyInterleavingTasteGate_single_carrier_alignment_decode_encode_bhist H,
        RegularCauchyInterleavingTasteGate_single_carrier_alignment_decode_encode_bhist C,
        RegularCauchyInterleavingTasteGate_single_carrier_alignment_decode_encode_bhist P,
        RegularCauchyInterleavingTasteGate_single_carrier_alignment_decode_encode_bhist N]

private theorem RegularCauchyInterleavingTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyInterleavingUp} :
    RegularCauchyInterleavingTasteGate_single_carrier_alignment_toEventFlow x =
      RegularCauchyInterleavingTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      RegularCauchyInterleavingTasteGate_single_carrier_alignment_fromEventFlow
          (RegularCauchyInterleavingTasteGate_single_carrier_alignment_toEventFlow x) =
        RegularCauchyInterleavingTasteGate_single_carrier_alignment_fromEventFlow
          (RegularCauchyInterleavingTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg RegularCauchyInterleavingTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegularCauchyInterleavingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RegularCauchyInterleavingTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyInterleavingBHistCarrier :
    BHistCarrier RegularCauchyInterleavingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := RegularCauchyInterleavingTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := RegularCauchyInterleavingTasteGate_single_carrier_alignment_fromEventFlow

instance regularCauchyInterleavingChapterTasteGate :
    ChapterTasteGate RegularCauchyInterleavingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      RegularCauchyInterleavingTasteGate_single_carrier_alignment_fromEventFlow
        (RegularCauchyInterleavingTasteGate_single_carrier_alignment_toEventFlow x) =
          some x
    exact RegularCauchyInterleavingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyInterleavingTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchyInterleavingFieldFaithful :
    FieldFaithful RegularCauchyInterleavingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := RegularCauchyInterleavingTasteGate_single_carrier_alignment_fields
  field_faithful := by
    intro x y h
    cases x with
    | mk A₁ B₁ SA₁ SB₁ sigma₁ M₁ EA₁ EB₁ E₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk A₂ B₂ SA₂ SB₂ sigma₂ M₂ EA₂ EB₂ E₂ H₂ C₂ P₂ N₂ =>
            injection h with hA t1
            injection t1 with hB t2
            injection t2 with hSA t3
            injection t3 with hSB t4
            injection t4 with hsigma t5
            injection t5 with hM t6
            injection t6 with hEA t7
            injection t7 with hEB t8
            injection t8 with hE t9
            injection t9 with hH t10
            injection t10 with hC t11
            injection t11 with hP t12
            injection t12 with hN _
            subst hA
            subst hB
            subst hSA
            subst hSB
            subst hsigma
            subst hM
            subst hEA
            subst hEB
            subst hE
            subst hH
            subst hC
            subst hP
            subst hN
            rfl

instance regularCauchyInterleavingNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RegularCauchyInterleavingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyInterleavingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RegularCauchyInterleavingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RegularCauchyInterleavingTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegularCauchyInterleavingUp) ∧
      (∀ A B SA SB sigma M EA EB E H C P N : BHist,
        RegularCauchyInterleavingTasteGate_single_carrier_alignment_fields
          (RegularCauchyInterleavingUp.mk A B SA SB sigma M EA EB E H C P N) =
            [A, B, SA, SB, sigma, M, EA, EB, E, H, C, P, N]) ∧
        RegularCauchyInterleavingTasteGate_single_carrier_alignment_decodeBHist
          (RegularCauchyInterleavingTasteGate_single_carrier_alignment_encodeBHist
            BHist.Empty) = BHist.Empty := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨regularCauchyInterleavingChapterTasteGate⟩
  · constructor
    · intro A B SA SB sigma M EA EB E H C P N
      rfl
    · rfl

end BEDC.Derived.RegularCauchyInterleavingUp
