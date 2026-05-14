import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySharedTailModulusUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySharedTailModulusUp : Type where
  | mk :
      (r0 r1 m0 m1 tau d w0 w1 q0 q1 e h c p n : BHist) →
      CauchySharedTailModulusUp
  deriving DecidableEq

def cauchySharedTailModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySharedTailModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySharedTailModulusEncodeBHist h

def cauchySharedTailModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySharedTailModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySharedTailModulusDecodeBHist tail)

private theorem cauchySharedTailModulusDecodeEncodeBHist :
    ∀ h : BHist,
      cauchySharedTailModulusDecodeBHist
        (cauchySharedTailModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchySharedTailModulusFields :
    CauchySharedTailModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySharedTailModulusUp.mk r0 r1 m0 m1 tau d w0 w1 q0 q1 e h c p n =>
      [r0, r1, m0, m1, tau, d, w0, w1, q0, q1, e, h, c, p, n]

def cauchySharedTailModulusSealRoute :
    CauchySharedTailModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySharedTailModulusUp.mk _r0 _r1 m0 m1 tau d w0 w1 q0 q1 e h c p n =>
      [m0, m1, tau, d, w0, w1, q0, q1, e, h, c, p, n]

def cauchySharedTailModulusToEventFlow :
    CauchySharedTailModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchySharedTailModulusFields x).map cauchySharedTailModulusEncodeBHist

def cauchySharedTailModulusFromEventFlow :
    EventFlow → Option CauchySharedTailModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | r0 :: rest0 =>
      match rest0 with
      | [] => none
      | r1 :: rest1 =>
          match rest1 with
          | [] => none
          | m0 :: rest2 =>
              match rest2 with
              | [] => none
              | m1 :: rest3 =>
                  match rest3 with
                  | [] => none
                  | tau :: rest4 =>
                      match rest4 with
                      | [] => none
                      | d :: rest5 =>
                          match rest5 with
                          | [] => none
                          | w0 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | w1 :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | q0 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | q1 :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | e :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | h :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | c :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | p :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | n :: rest14 =>
                                                              match rest14 with
                                                              | [] =>
                                                                  some
                                                                    (CauchySharedTailModulusUp.mk
                                                                      (cauchySharedTailModulusDecodeBHist
                                                                        r0)
                                                                      (cauchySharedTailModulusDecodeBHist
                                                                        r1)
                                                                      (cauchySharedTailModulusDecodeBHist
                                                                        m0)
                                                                      (cauchySharedTailModulusDecodeBHist
                                                                        m1)
                                                                      (cauchySharedTailModulusDecodeBHist
                                                                        tau)
                                                                      (cauchySharedTailModulusDecodeBHist
                                                                        d)
                                                                      (cauchySharedTailModulusDecodeBHist
                                                                        w0)
                                                                      (cauchySharedTailModulusDecodeBHist
                                                                        w1)
                                                                      (cauchySharedTailModulusDecodeBHist
                                                                        q0)
                                                                      (cauchySharedTailModulusDecodeBHist
                                                                        q1)
                                                                      (cauchySharedTailModulusDecodeBHist
                                                                        e)
                                                                      (cauchySharedTailModulusDecodeBHist
                                                                        h)
                                                                      (cauchySharedTailModulusDecodeBHist
                                                                        c)
                                                                      (cauchySharedTailModulusDecodeBHist
                                                                        p)
                                                                      (cauchySharedTailModulusDecodeBHist
                                                                        n))
                                                              | _ :: _ => none

private theorem cauchySharedTailModulus_round_trip :
    ∀ x : CauchySharedTailModulusUp,
      cauchySharedTailModulusFromEventFlow
        (cauchySharedTailModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk r0 r1 m0 m1 tau d w0 w1 q0 q1 e h c p n =>
      change
        some
          (CauchySharedTailModulusUp.mk
            (cauchySharedTailModulusDecodeBHist
              (cauchySharedTailModulusEncodeBHist r0))
            (cauchySharedTailModulusDecodeBHist
              (cauchySharedTailModulusEncodeBHist r1))
            (cauchySharedTailModulusDecodeBHist
              (cauchySharedTailModulusEncodeBHist m0))
            (cauchySharedTailModulusDecodeBHist
              (cauchySharedTailModulusEncodeBHist m1))
            (cauchySharedTailModulusDecodeBHist
              (cauchySharedTailModulusEncodeBHist tau))
            (cauchySharedTailModulusDecodeBHist
              (cauchySharedTailModulusEncodeBHist d))
            (cauchySharedTailModulusDecodeBHist
              (cauchySharedTailModulusEncodeBHist w0))
            (cauchySharedTailModulusDecodeBHist
              (cauchySharedTailModulusEncodeBHist w1))
            (cauchySharedTailModulusDecodeBHist
              (cauchySharedTailModulusEncodeBHist q0))
            (cauchySharedTailModulusDecodeBHist
              (cauchySharedTailModulusEncodeBHist q1))
            (cauchySharedTailModulusDecodeBHist
              (cauchySharedTailModulusEncodeBHist e))
            (cauchySharedTailModulusDecodeBHist
              (cauchySharedTailModulusEncodeBHist h))
            (cauchySharedTailModulusDecodeBHist
              (cauchySharedTailModulusEncodeBHist c))
            (cauchySharedTailModulusDecodeBHist
              (cauchySharedTailModulusEncodeBHist p))
            (cauchySharedTailModulusDecodeBHist
              (cauchySharedTailModulusEncodeBHist n))) =
          some (CauchySharedTailModulusUp.mk r0 r1 m0 m1 tau d w0 w1 q0 q1 e h c p n)
      rw [cauchySharedTailModulusDecodeEncodeBHist r0,
        cauchySharedTailModulusDecodeEncodeBHist r1,
        cauchySharedTailModulusDecodeEncodeBHist m0,
        cauchySharedTailModulusDecodeEncodeBHist m1,
        cauchySharedTailModulusDecodeEncodeBHist tau,
        cauchySharedTailModulusDecodeEncodeBHist d,
        cauchySharedTailModulusDecodeEncodeBHist w0,
        cauchySharedTailModulusDecodeEncodeBHist w1,
        cauchySharedTailModulusDecodeEncodeBHist q0,
        cauchySharedTailModulusDecodeEncodeBHist q1,
        cauchySharedTailModulusDecodeEncodeBHist e,
        cauchySharedTailModulusDecodeEncodeBHist h,
        cauchySharedTailModulusDecodeEncodeBHist c,
        cauchySharedTailModulusDecodeEncodeBHist p,
        cauchySharedTailModulusDecodeEncodeBHist n]

private theorem cauchySharedTailModulusToEventFlow_injective
    {x y : CauchySharedTailModulusUp} :
    cauchySharedTailModulusToEventFlow x =
      cauchySharedTailModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySharedTailModulusFromEventFlow
          (cauchySharedTailModulusToEventFlow x) =
        cauchySharedTailModulusFromEventFlow
          (cauchySharedTailModulusToEventFlow y) :=
    congrArg cauchySharedTailModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchySharedTailModulus_round_trip x).symm
      (Eq.trans hread (cauchySharedTailModulus_round_trip y)))

private theorem cauchySharedTailModulus_fields_faithful :
    ∀ x y : CauchySharedTailModulusUp,
      cauchySharedTailModulusFields x =
        cauchySharedTailModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk r0₁ r1₁ m0₁ m1₁ tau₁ d₁ w0₁ w1₁ q0₁ q1₁ e₁ h₁ c₁ p₁ n₁ =>
      cases y with
      | mk r0₂ r1₂ m0₂ m1₂ tau₂ d₂ w0₂ w1₂ q0₂ q1₂ e₂ h₂ c₂ p₂ n₂ =>
          injection hfields with hr0 tail0
          injection tail0 with hr1 tail1
          injection tail1 with hm0 tail2
          injection tail2 with hm1 tail3
          injection tail3 with htau tail4
          injection tail4 with hd tail5
          injection tail5 with hw0 tail6
          injection tail6 with hw1 tail7
          injection tail7 with hq0 tail8
          injection tail8 with hq1 tail9
          injection tail9 with he tail10
          injection tail10 with hh tail11
          injection tail11 with hc tail12
          injection tail12 with hp tail13
          injection tail13 with hn _
          subst hr0
          subst hr1
          subst hm0
          subst hm1
          subst htau
          subst hd
          subst hw0
          subst hw1
          subst hq0
          subst hq1
          subst he
          subst hh
          subst hc
          subst hp
          subst hn
          rfl

instance cauchySharedTailModulusBHistCarrier :
    BHistCarrier CauchySharedTailModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySharedTailModulusToEventFlow
  fromEventFlow := cauchySharedTailModulusFromEventFlow

instance cauchySharedTailModulusChapterTasteGate :
    ChapterTasteGate CauchySharedTailModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchySharedTailModulusFromEventFlow
      (cauchySharedTailModulusToEventFlow x) = some x
    exact cauchySharedTailModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchySharedTailModulusToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchySharedTailModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchySharedTailModulusFromEventFlow
      (cauchySharedTailModulusToEventFlow x) = some x
    exact cauchySharedTailModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchySharedTailModulusToEventFlow_injective heq)

instance cauchySharedTailModulusFieldFaithful :
    FieldFaithful CauchySharedTailModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchySharedTailModulusFields
  field_faithful := cauchySharedTailModulus_fields_faithful

instance cauchySharedTailModulusNontrivial :
    Nontrivial CauchySharedTailModulusUp where
  witness_pair :=
    ⟨CauchySharedTailModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchySharedTailModulusUp.mk BHist.Empty BHist.Empty (BHist.e0 BHist.Empty)
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

theorem CauchySharedTailModulusTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CauchySharedTailModulusUp) ∧
      Nonempty (ChapterTasteGate CauchySharedTailModulusUp) ∧
        Nonempty (FieldFaithful CauchySharedTailModulusUp) ∧
          Nonempty (Nontrivial CauchySharedTailModulusUp) ∧
            cauchySharedTailModulusEncodeBHist BHist.Empty = ([] : RawEvent) ∧
              cauchySharedTailModulusEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨cauchySharedTailModulusBHistCarrier⟩
  · constructor
    · exact ⟨cauchySharedTailModulusChapterTasteGate⟩
    · constructor
      · exact ⟨cauchySharedTailModulusFieldFaithful⟩
      · constructor
        · exact ⟨cauchySharedTailModulusNontrivial⟩
        · constructor
          · rfl
          · rfl

theorem CauchySharedTailModulusCarrier_real_seal_handoff
    (x : CauchySharedTailModulusUp) :
    ∃ m0 m1 tau d w0 w1 q0 q1 e h c p n : BHist,
      cauchySharedTailModulusSealRoute x =
          [m0, m1, tau, d, w0, w1, q0, q1, e, h, c, p, n] ∧
        Cont m0 tau (append m0 tau) ∧
          Cont m1 tau (append m1 tau) ∧
            BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk r0 r1 m0 m1 tau d w0 w1 q0 q1 e h c p n =>
      refine ⟨m0, m1, tau, d, w0, w1, q0, q1, e, h, c, p, n, ?_⟩
      constructor
      · rfl
      · constructor
        · rfl
        · constructor
          · rfl
          · change
              cauchySharedTailModulusFromEventFlow
                  (cauchySharedTailModulusToEventFlow
                    (CauchySharedTailModulusUp.mk r0 r1 m0 m1 tau d w0 w1 q0 q1 e h c p n)) =
                some
                  (CauchySharedTailModulusUp.mk r0 r1 m0 m1 tau d w0 w1 q0 q1 e h c p n)
            exact cauchySharedTailModulus_round_trip
              (CauchySharedTailModulusUp.mk r0 r1 m0 m1 tau d w0 w1 q0 q1 e h c p n)

end BEDC.Derived.CauchySharedTailModulusUp
