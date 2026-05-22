import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealPolynomialUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealPolynomialUp : Type where
  | mk (A X Q S G W D E M H C P N : BHist) : RealPolynomialUp
  deriving DecidableEq

def realPolynomialEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realPolynomialEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realPolynomialEncodeBHist h

def realPolynomialDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realPolynomialDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realPolynomialDecodeBHist tail)

private theorem RealPolynomialUpTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, realPolynomialDecodeBHist (realPolynomialEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realPolynomialFields : RealPolynomialUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealPolynomialUp.mk A X Q S G W D E M H C P N =>
      [A, X, Q, S, G, W, D, E, M, H, C, P, N]

def realPolynomialToEventFlow : RealPolynomialUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realPolynomialFields x).map realPolynomialEncodeBHist

def realPolynomialFromEventFlow : EventFlow → Option RealPolynomialUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | A :: rest0 =>
      match rest0 with
      | [] => none
      | X :: rest1 =>
          match rest1 with
          | [] => none
          | Q :: rest2 =>
              match rest2 with
              | [] => none
              | S :: rest3 =>
                  match rest3 with
                  | [] => none
                  | G :: rest4 =>
                      match rest4 with
                      | [] => none
                      | W :: rest5 =>
                          match rest5 with
                          | [] => none
                          | D :: rest6 =>
                              match rest6 with
                              | [] => none
                              | E :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | M :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | H :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | C :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | P :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | N :: rest12 =>
                                                      match rest12 with
                                                      | [] =>
                                                          some
                                                            (RealPolynomialUp.mk
                                                              (realPolynomialDecodeBHist A)
                                                              (realPolynomialDecodeBHist X)
                                                              (realPolynomialDecodeBHist Q)
                                                              (realPolynomialDecodeBHist S)
                                                              (realPolynomialDecodeBHist G)
                                                              (realPolynomialDecodeBHist W)
                                                              (realPolynomialDecodeBHist D)
                                                              (realPolynomialDecodeBHist E)
                                                              (realPolynomialDecodeBHist M)
                                                              (realPolynomialDecodeBHist H)
                                                              (realPolynomialDecodeBHist C)
                                                              (realPolynomialDecodeBHist P)
                                                              (realPolynomialDecodeBHist N))
                                                      | _ :: _ => none

private theorem RealPolynomialUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealPolynomialUp,
      realPolynomialFromEventFlow (realPolynomialToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A X Q S G W D E M H C P N =>
      change
        some
          (RealPolynomialUp.mk
            (realPolynomialDecodeBHist (realPolynomialEncodeBHist A))
            (realPolynomialDecodeBHist (realPolynomialEncodeBHist X))
            (realPolynomialDecodeBHist (realPolynomialEncodeBHist Q))
            (realPolynomialDecodeBHist (realPolynomialEncodeBHist S))
            (realPolynomialDecodeBHist (realPolynomialEncodeBHist G))
            (realPolynomialDecodeBHist (realPolynomialEncodeBHist W))
            (realPolynomialDecodeBHist (realPolynomialEncodeBHist D))
            (realPolynomialDecodeBHist (realPolynomialEncodeBHist E))
            (realPolynomialDecodeBHist (realPolynomialEncodeBHist M))
            (realPolynomialDecodeBHist (realPolynomialEncodeBHist H))
            (realPolynomialDecodeBHist (realPolynomialEncodeBHist C))
            (realPolynomialDecodeBHist (realPolynomialEncodeBHist P))
            (realPolynomialDecodeBHist (realPolynomialEncodeBHist N))) =
          some (RealPolynomialUp.mk A X Q S G W D E M H C P N)
      rw [RealPolynomialUpTasteGate_single_carrier_alignment_decode A,
        RealPolynomialUpTasteGate_single_carrier_alignment_decode X,
        RealPolynomialUpTasteGate_single_carrier_alignment_decode Q,
        RealPolynomialUpTasteGate_single_carrier_alignment_decode S,
        RealPolynomialUpTasteGate_single_carrier_alignment_decode G,
        RealPolynomialUpTasteGate_single_carrier_alignment_decode W,
        RealPolynomialUpTasteGate_single_carrier_alignment_decode D,
        RealPolynomialUpTasteGate_single_carrier_alignment_decode E,
        RealPolynomialUpTasteGate_single_carrier_alignment_decode M,
        RealPolynomialUpTasteGate_single_carrier_alignment_decode H,
        RealPolynomialUpTasteGate_single_carrier_alignment_decode C,
        RealPolynomialUpTasteGate_single_carrier_alignment_decode P,
        RealPolynomialUpTasteGate_single_carrier_alignment_decode N]

private theorem RealPolynomialUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealPolynomialUp} :
    realPolynomialToEventFlow x = realPolynomialToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realPolynomialFromEventFlow (realPolynomialToEventFlow x) =
        realPolynomialFromEventFlow (realPolynomialToEventFlow y) :=
    congrArg realPolynomialFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealPolynomialUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealPolynomialUpTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealPolynomialUpTasteGate_single_carrier_alignment_fields :
    ∀ x y : RealPolynomialUp, realPolynomialFields x = realPolynomialFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A₁ X₁ Q₁ S₁ G₁ W₁ D₁ E₁ M₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk A₂ X₂ Q₂ S₂ G₂ W₂ D₂ E₂ M₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hA tail0
          injection tail0 with hX tail1
          injection tail1 with hQ tail2
          injection tail2 with hS tail3
          injection tail3 with hG tail4
          injection tail4 with hW tail5
          injection tail5 with hD tail6
          injection tail6 with hE tail7
          injection tail7 with hM tail8
          injection tail8 with hH tail9
          injection tail9 with hC tail10
          injection tail10 with hP tail11
          injection tail11 with hN _
          subst hA
          subst hX
          subst hQ
          subst hS
          subst hG
          subst hW
          subst hD
          subst hE
          subst hM
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance realPolynomialBHistCarrier : BHistCarrier RealPolynomialUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realPolynomialToEventFlow
  fromEventFlow := realPolynomialFromEventFlow

instance realPolynomialChapterTasteGate : ChapterTasteGate RealPolynomialUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realPolynomialFromEventFlow (realPolynomialToEventFlow x) = some x
    exact RealPolynomialUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealPolynomialUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realPolynomialFieldFaithful : FieldFaithful RealPolynomialUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realPolynomialFields
  field_faithful := RealPolynomialUpTasteGate_single_carrier_alignment_fields

instance realPolynomialNontrivial : Nontrivial RealPolynomialUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealPolynomialUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealPolynomialUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealPolynomialUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realPolynomialChapterTasteGate

theorem RealPolynomialUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, realPolynomialDecodeBHist (realPolynomialEncodeBHist h) = h) ∧
      (∀ x : RealPolynomialUp,
        realPolynomialFromEventFlow (realPolynomialToEventFlow x) = some x) ∧
        (∀ x y : RealPolynomialUp,
          realPolynomialToEventFlow x = realPolynomialToEventFlow y → x = y) ∧
          realPolynomialEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨RealPolynomialUpTasteGate_single_carrier_alignment_decode,
      RealPolynomialUpTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => RealPolynomialUpTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealPolynomialUp
