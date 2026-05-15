import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyTailModulusFusionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyTailModulusFusionUp : Type where
  | mk (T0 T1 mu0 mu1 tau V W0 W1 D0 D1 Q0 Q1 E H C P N : BHist) :
      CauchyTailModulusFusionUp
  deriving DecidableEq

def cauchyTailModulusFusionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyTailModulusFusionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyTailModulusFusionEncodeBHist h

def cauchyTailModulusFusionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyTailModulusFusionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyTailModulusFusionDecodeBHist tail)

private theorem cauchyTailModulusFusionDecode_encode_bhist :
    ∀ h : BHist, cauchyTailModulusFusionDecodeBHist
      (cauchyTailModulusFusionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyTailModulusFusionToEventFlow : CauchyTailModulusFusionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyTailModulusFusionUp.mk T0 T1 mu0 mu1 tau V W0 W1 D0 D1 Q0 Q1 E H C P N =>
      [cauchyTailModulusFusionEncodeBHist T0,
        cauchyTailModulusFusionEncodeBHist T1,
        cauchyTailModulusFusionEncodeBHist mu0,
        cauchyTailModulusFusionEncodeBHist mu1,
        cauchyTailModulusFusionEncodeBHist tau,
        cauchyTailModulusFusionEncodeBHist V,
        cauchyTailModulusFusionEncodeBHist W0,
        cauchyTailModulusFusionEncodeBHist W1,
        cauchyTailModulusFusionEncodeBHist D0,
        cauchyTailModulusFusionEncodeBHist D1,
        cauchyTailModulusFusionEncodeBHist Q0,
        cauchyTailModulusFusionEncodeBHist Q1,
        cauchyTailModulusFusionEncodeBHist E,
        cauchyTailModulusFusionEncodeBHist H,
        cauchyTailModulusFusionEncodeBHist C,
        cauchyTailModulusFusionEncodeBHist P,
        cauchyTailModulusFusionEncodeBHist N]

def cauchyTailModulusFusionFromEventFlow : EventFlow → Option CauchyTailModulusFusionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | T0 :: rest0 =>
      match rest0 with
      | [] => none
      | T1 :: rest1 =>
          match rest1 with
          | [] => none
          | mu0 :: rest2 =>
              match rest2 with
              | [] => none
              | mu1 :: rest3 =>
                  match rest3 with
                  | [] => none
                  | tau :: rest4 =>
                      match rest4 with
                      | [] => none
                      | V :: rest5 =>
                          match rest5 with
                          | [] => none
                          | W0 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | W1 :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | D0 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | D1 :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | Q0 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | Q1 :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | E :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | H :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | C :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | P :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | N :: rest16 =>
                                                                      match rest16 with
                                                                      | [] =>
                                                                          some
                                                                            (CauchyTailModulusFusionUp.mk
                                                                              (cauchyTailModulusFusionDecodeBHist T0)
                                                                              (cauchyTailModulusFusionDecodeBHist T1)
                                                                              (cauchyTailModulusFusionDecodeBHist mu0)
                                                                              (cauchyTailModulusFusionDecodeBHist mu1)
                                                                              (cauchyTailModulusFusionDecodeBHist tau)
                                                                              (cauchyTailModulusFusionDecodeBHist V)
                                                                              (cauchyTailModulusFusionDecodeBHist W0)
                                                                              (cauchyTailModulusFusionDecodeBHist W1)
                                                                              (cauchyTailModulusFusionDecodeBHist D0)
                                                                              (cauchyTailModulusFusionDecodeBHist D1)
                                                                              (cauchyTailModulusFusionDecodeBHist Q0)
                                                                              (cauchyTailModulusFusionDecodeBHist Q1)
                                                                              (cauchyTailModulusFusionDecodeBHist E)
                                                                              (cauchyTailModulusFusionDecodeBHist H)
                                                                              (cauchyTailModulusFusionDecodeBHist C)
                                                                              (cauchyTailModulusFusionDecodeBHist P)
                                                                              (cauchyTailModulusFusionDecodeBHist N))
                                                                      | _ :: _ => none

private theorem cauchyTailModulusFusion_round_trip :
    ∀ x : CauchyTailModulusFusionUp,
      cauchyTailModulusFusionFromEventFlow (cauchyTailModulusFusionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T0 T1 mu0 mu1 tau V W0 W1 D0 D1 Q0 Q1 E H C P N =>
      change
        some
          (CauchyTailModulusFusionUp.mk
            (cauchyTailModulusFusionDecodeBHist (cauchyTailModulusFusionEncodeBHist T0))
            (cauchyTailModulusFusionDecodeBHist (cauchyTailModulusFusionEncodeBHist T1))
            (cauchyTailModulusFusionDecodeBHist (cauchyTailModulusFusionEncodeBHist mu0))
            (cauchyTailModulusFusionDecodeBHist (cauchyTailModulusFusionEncodeBHist mu1))
            (cauchyTailModulusFusionDecodeBHist (cauchyTailModulusFusionEncodeBHist tau))
            (cauchyTailModulusFusionDecodeBHist (cauchyTailModulusFusionEncodeBHist V))
            (cauchyTailModulusFusionDecodeBHist (cauchyTailModulusFusionEncodeBHist W0))
            (cauchyTailModulusFusionDecodeBHist (cauchyTailModulusFusionEncodeBHist W1))
            (cauchyTailModulusFusionDecodeBHist (cauchyTailModulusFusionEncodeBHist D0))
            (cauchyTailModulusFusionDecodeBHist (cauchyTailModulusFusionEncodeBHist D1))
            (cauchyTailModulusFusionDecodeBHist (cauchyTailModulusFusionEncodeBHist Q0))
            (cauchyTailModulusFusionDecodeBHist (cauchyTailModulusFusionEncodeBHist Q1))
            (cauchyTailModulusFusionDecodeBHist (cauchyTailModulusFusionEncodeBHist E))
            (cauchyTailModulusFusionDecodeBHist (cauchyTailModulusFusionEncodeBHist H))
            (cauchyTailModulusFusionDecodeBHist (cauchyTailModulusFusionEncodeBHist C))
            (cauchyTailModulusFusionDecodeBHist (cauchyTailModulusFusionEncodeBHist P))
            (cauchyTailModulusFusionDecodeBHist (cauchyTailModulusFusionEncodeBHist N))) =
          some (CauchyTailModulusFusionUp.mk T0 T1 mu0 mu1 tau V W0 W1 D0 D1 Q0 Q1
            E H C P N)
      rw [cauchyTailModulusFusionDecode_encode_bhist T0,
        cauchyTailModulusFusionDecode_encode_bhist T1,
        cauchyTailModulusFusionDecode_encode_bhist mu0,
        cauchyTailModulusFusionDecode_encode_bhist mu1,
        cauchyTailModulusFusionDecode_encode_bhist tau,
        cauchyTailModulusFusionDecode_encode_bhist V,
        cauchyTailModulusFusionDecode_encode_bhist W0,
        cauchyTailModulusFusionDecode_encode_bhist W1,
        cauchyTailModulusFusionDecode_encode_bhist D0,
        cauchyTailModulusFusionDecode_encode_bhist D1,
        cauchyTailModulusFusionDecode_encode_bhist Q0,
        cauchyTailModulusFusionDecode_encode_bhist Q1,
        cauchyTailModulusFusionDecode_encode_bhist E,
        cauchyTailModulusFusionDecode_encode_bhist H,
        cauchyTailModulusFusionDecode_encode_bhist C,
        cauchyTailModulusFusionDecode_encode_bhist P,
        cauchyTailModulusFusionDecode_encode_bhist N]

private theorem cauchyTailModulusFusionToEventFlow_injective
    {x y : CauchyTailModulusFusionUp} :
    cauchyTailModulusFusionToEventFlow x = cauchyTailModulusFusionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyTailModulusFusionFromEventFlow (cauchyTailModulusFusionToEventFlow x) =
        cauchyTailModulusFusionFromEventFlow (cauchyTailModulusFusionToEventFlow y) :=
    congrArg cauchyTailModulusFusionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyTailModulusFusion_round_trip x).symm
      (Eq.trans hread (cauchyTailModulusFusion_round_trip y)))

instance cauchyTailModulusFusionBHistCarrier : BHistCarrier CauchyTailModulusFusionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyTailModulusFusionToEventFlow
  fromEventFlow := cauchyTailModulusFusionFromEventFlow

instance cauchyTailModulusFusionChapterTasteGate :
    ChapterTasteGate CauchyTailModulusFusionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyTailModulusFusionFromEventFlow
      (cauchyTailModulusFusionToEventFlow x) = some x
    exact cauchyTailModulusFusion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyTailModulusFusionToEventFlow_injective heq)

instance cauchyTailModulusFusionFieldFaithful : FieldFaithful CauchyTailModulusFusionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | CauchyTailModulusFusionUp.mk T0 T1 mu0 mu1 tau V W0 W1 D0 D1 Q0 Q1 E H C P N =>
        [T0, T1, mu0, mu1, tau, V, W0, W1, D0, D1, Q0, Q1, E, H, C, P, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk T0₁ T1₁ mu0₁ mu1₁ tau₁ V₁ W0₁ W1₁ D0₁ D1₁ Q0₁ Q1₁ E₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk T0₂ T1₂ mu0₂ mu1₂ tau₂ V₂ W0₂ W1₂ D0₂ D1₂ Q0₂ Q1₂ E₂ H₂ C₂ P₂ N₂ =>
            simp only [] at h
            cases h
            rfl

theorem CauchyTailModulusFusionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        cauchyTailModulusFusionDecodeBHist (cauchyTailModulusFusionEncodeBHist h) = h) ∧
      (∀ x : CauchyTailModulusFusionUp,
        cauchyTailModulusFusionFromEventFlow (cauchyTailModulusFusionToEventFlow x) =
          some x) ∧
      (∀ x y : CauchyTailModulusFusionUp,
        cauchyTailModulusFusionToEventFlow x = cauchyTailModulusFusionToEventFlow y →
          x = y) ∧
      cauchyTailModulusFusionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨cauchyTailModulusFusionDecode_encode_bhist, cauchyTailModulusFusion_round_trip,
    fun _ _ heq => cauchyTailModulusFusionToEventFlow_injective heq, rfl⟩

end BEDC.Derived.CauchyTailModulusFusionUp
