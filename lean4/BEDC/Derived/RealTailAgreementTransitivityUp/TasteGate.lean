import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealTailAgreementTransitivityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealTailAgreementTransitivityUp : Type where
  | mk :
      (r0 r1 r2 w01 w12 d01 d12 a01 a12 m h c p n : BHist) →
      RealTailAgreementTransitivityUp
  deriving DecidableEq

def realTailAgreementTransitivityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realTailAgreementTransitivityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realTailAgreementTransitivityEncodeBHist h

def realTailAgreementTransitivityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realTailAgreementTransitivityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realTailAgreementTransitivityDecodeBHist tail)

private theorem realTailAgreementTransitivityDecodeEncodeBHist :
    ∀ h : BHist,
      realTailAgreementTransitivityDecodeBHist
        (realTailAgreementTransitivityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realTailAgreementTransitivityFields :
    RealTailAgreementTransitivityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealTailAgreementTransitivityUp.mk r0 r1 r2 w01 w12 d01 d12 a01 a12 m h c p n =>
      [r0, r1, r2, w01, w12, d01, d12, a01, a12, m, h, c, p, n]

def realTailAgreementTransitivityToEventFlow :
    RealTailAgreementTransitivityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (realTailAgreementTransitivityFields x).map realTailAgreementTransitivityEncodeBHist

def realTailAgreementTransitivityFromEventFlow :
    EventFlow → Option RealTailAgreementTransitivityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | r0 :: rest0 =>
      match rest0 with
      | [] => none
      | r1 :: rest1 =>
          match rest1 with
          | [] => none
          | r2 :: rest2 =>
              match rest2 with
              | [] => none
              | w01 :: rest3 =>
                  match rest3 with
                  | [] => none
                  | w12 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | d01 :: rest5 =>
                          match rest5 with
                          | [] => none
                          | d12 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | a01 :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | a12 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | m :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | h :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | c :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | p :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | n :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (RealTailAgreementTransitivityUp.mk
                                                                  (realTailAgreementTransitivityDecodeBHist r0)
                                                                  (realTailAgreementTransitivityDecodeBHist r1)
                                                                  (realTailAgreementTransitivityDecodeBHist r2)
                                                                  (realTailAgreementTransitivityDecodeBHist w01)
                                                                  (realTailAgreementTransitivityDecodeBHist w12)
                                                                  (realTailAgreementTransitivityDecodeBHist d01)
                                                                  (realTailAgreementTransitivityDecodeBHist d12)
                                                                  (realTailAgreementTransitivityDecodeBHist a01)
                                                                  (realTailAgreementTransitivityDecodeBHist a12)
                                                                  (realTailAgreementTransitivityDecodeBHist m)
                                                                  (realTailAgreementTransitivityDecodeBHist h)
                                                                  (realTailAgreementTransitivityDecodeBHist c)
                                                                  (realTailAgreementTransitivityDecodeBHist p)
                                                                  (realTailAgreementTransitivityDecodeBHist n))
                                                          | _ :: _ => none

private theorem realTailAgreementTransitivity_round_trip :
    ∀ x : RealTailAgreementTransitivityUp,
      realTailAgreementTransitivityFromEventFlow
          (realTailAgreementTransitivityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk r0 r1 r2 w01 w12 d01 d12 a01 a12 m h c p n =>
      change
        some
          (RealTailAgreementTransitivityUp.mk
            (realTailAgreementTransitivityDecodeBHist
              (realTailAgreementTransitivityEncodeBHist r0))
            (realTailAgreementTransitivityDecodeBHist
              (realTailAgreementTransitivityEncodeBHist r1))
            (realTailAgreementTransitivityDecodeBHist
              (realTailAgreementTransitivityEncodeBHist r2))
            (realTailAgreementTransitivityDecodeBHist
              (realTailAgreementTransitivityEncodeBHist w01))
            (realTailAgreementTransitivityDecodeBHist
              (realTailAgreementTransitivityEncodeBHist w12))
            (realTailAgreementTransitivityDecodeBHist
              (realTailAgreementTransitivityEncodeBHist d01))
            (realTailAgreementTransitivityDecodeBHist
              (realTailAgreementTransitivityEncodeBHist d12))
            (realTailAgreementTransitivityDecodeBHist
              (realTailAgreementTransitivityEncodeBHist a01))
            (realTailAgreementTransitivityDecodeBHist
              (realTailAgreementTransitivityEncodeBHist a12))
            (realTailAgreementTransitivityDecodeBHist
              (realTailAgreementTransitivityEncodeBHist m))
            (realTailAgreementTransitivityDecodeBHist
              (realTailAgreementTransitivityEncodeBHist h))
            (realTailAgreementTransitivityDecodeBHist
              (realTailAgreementTransitivityEncodeBHist c))
            (realTailAgreementTransitivityDecodeBHist
              (realTailAgreementTransitivityEncodeBHist p))
            (realTailAgreementTransitivityDecodeBHist
              (realTailAgreementTransitivityEncodeBHist n))) =
          some (RealTailAgreementTransitivityUp.mk r0 r1 r2 w01 w12 d01 d12 a01 a12
            m h c p n)
      rw [realTailAgreementTransitivityDecodeEncodeBHist r0,
        realTailAgreementTransitivityDecodeEncodeBHist r1,
        realTailAgreementTransitivityDecodeEncodeBHist r2,
        realTailAgreementTransitivityDecodeEncodeBHist w01,
        realTailAgreementTransitivityDecodeEncodeBHist w12,
        realTailAgreementTransitivityDecodeEncodeBHist d01,
        realTailAgreementTransitivityDecodeEncodeBHist d12,
        realTailAgreementTransitivityDecodeEncodeBHist a01,
        realTailAgreementTransitivityDecodeEncodeBHist a12,
        realTailAgreementTransitivityDecodeEncodeBHist m,
        realTailAgreementTransitivityDecodeEncodeBHist h,
        realTailAgreementTransitivityDecodeEncodeBHist c,
        realTailAgreementTransitivityDecodeEncodeBHist p,
        realTailAgreementTransitivityDecodeEncodeBHist n]

private theorem realTailAgreementTransitivityToEventFlow_injective
    {x y : RealTailAgreementTransitivityUp} :
    realTailAgreementTransitivityToEventFlow x =
      realTailAgreementTransitivityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realTailAgreementTransitivityFromEventFlow
          (realTailAgreementTransitivityToEventFlow x) =
        realTailAgreementTransitivityFromEventFlow
          (realTailAgreementTransitivityToEventFlow y) :=
    congrArg realTailAgreementTransitivityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realTailAgreementTransitivity_round_trip x).symm
      (Eq.trans hread (realTailAgreementTransitivity_round_trip y)))

private theorem realTailAgreementTransitivity_fields_faithful :
    ∀ x y : RealTailAgreementTransitivityUp,
      realTailAgreementTransitivityFields x =
        realTailAgreementTransitivityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk r0₁ r1₁ r2₁ w01₁ w12₁ d01₁ d12₁ a01₁ a12₁ m₁ h₁ c₁ p₁ n₁ =>
      cases y with
      | mk r0₂ r1₂ r2₂ w01₂ w12₂ d01₂ d12₂ a01₂ a12₂ m₂ h₂ c₂ p₂ n₂ =>
          injection hfields with hr0 t0
          injection t0 with hr1 t1
          injection t1 with hr2 t2
          injection t2 with hw01 t3
          injection t3 with hw12 t4
          injection t4 with hd01 t5
          injection t5 with hd12 t6
          injection t6 with ha01 t7
          injection t7 with ha12 t8
          injection t8 with hm t9
          injection t9 with hh t10
          injection t10 with hc t11
          injection t11 with hp t12
          injection t12 with hn _
          subst hr0
          subst hr1
          subst hr2
          subst hw01
          subst hw12
          subst hd01
          subst hd12
          subst ha01
          subst ha12
          subst hm
          subst hh
          subst hc
          subst hp
          subst hn
          rfl

instance realTailAgreementTransitivityBHistCarrier :
    BHistCarrier RealTailAgreementTransitivityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realTailAgreementTransitivityToEventFlow
  fromEventFlow := realTailAgreementTransitivityFromEventFlow

instance realTailAgreementTransitivityChapterTasteGate :
    ChapterTasteGate RealTailAgreementTransitivityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realTailAgreementTransitivityFromEventFlow
        (realTailAgreementTransitivityToEventFlow x) = some x
    exact realTailAgreementTransitivity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realTailAgreementTransitivityToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealTailAgreementTransitivityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realTailAgreementTransitivityFromEventFlow
        (realTailAgreementTransitivityToEventFlow x) = some x
    exact realTailAgreementTransitivity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realTailAgreementTransitivityToEventFlow_injective heq)

instance realTailAgreementTransitivityFieldFaithful :
    FieldFaithful RealTailAgreementTransitivityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realTailAgreementTransitivityFields
  field_faithful := realTailAgreementTransitivity_fields_faithful

instance realTailAgreementTransitivityNontrivial :
    Nontrivial RealTailAgreementTransitivityUp where
  witness_pair :=
    ⟨RealTailAgreementTransitivityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      RealTailAgreementTransitivityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

theorem RealTailAgreementTransitivityTasteGate_single_carrier_alignment :
    realTailAgreementTransitivityEncodeBHist BHist.Empty = ([] : List BMark) ∧
      (∀ h : BHist,
        realTailAgreementTransitivityDecodeBHist
          (realTailAgreementTransitivityEncodeBHist h) = h) ∧
        (∀ x : RealTailAgreementTransitivityUp,
          realTailAgreementTransitivityFromEventFlow
            (realTailAgreementTransitivityToEventFlow x) = some x) ∧
          (∀ {x y : RealTailAgreementTransitivityUp},
            realTailAgreementTransitivityToEventFlow x =
              realTailAgreementTransitivityToEventFlow y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · constructor
    · exact realTailAgreementTransitivityDecodeEncodeBHist
    · constructor
      · exact realTailAgreementTransitivity_round_trip
      · intro x y heq
        exact realTailAgreementTransitivityToEventFlow_injective heq

end BEDC.Derived.RealTailAgreementTransitivityUp
