import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealBolzanoUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealBolzanoUp : Type where
  | mk (a b L U S D J R E H C P N : BHist) : RealBolzanoUp
  deriving DecidableEq

def realBolzanoEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realBolzanoEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realBolzanoEncodeBHist h

def realBolzanoDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realBolzanoDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realBolzanoDecodeBHist tail)

private theorem RealBolzanoTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, realBolzanoDecodeBHist (realBolzanoEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realBolzanoFields : RealBolzanoUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealBolzanoUp.mk a b L U S D J R E H C P N => [a, b, L, U, S, D, J, R, E, H, C, P, N]

def realBolzanoToEventFlow : RealBolzanoUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realBolzanoFields x).map realBolzanoEncodeBHist

def realBolzanoFromEventFlow : EventFlow → Option RealBolzanoUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | a :: rest0 =>
      match rest0 with
      | [] => none
      | b :: rest1 =>
          match rest1 with
          | [] => none
          | L :: rest2 =>
              match rest2 with
              | [] => none
              | U :: rest3 =>
                  match rest3 with
                  | [] => none
                  | S :: rest4 =>
                      match rest4 with
                      | [] => none
                      | D :: rest5 =>
                          match rest5 with
                          | [] => none
                          | J :: rest6 =>
                              match rest6 with
                              | [] => none
                              | R :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | E :: rest8 =>
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
                                                            (RealBolzanoUp.mk
                                                              (realBolzanoDecodeBHist a)
                                                              (realBolzanoDecodeBHist b)
                                                              (realBolzanoDecodeBHist L)
                                                              (realBolzanoDecodeBHist U)
                                                              (realBolzanoDecodeBHist S)
                                                              (realBolzanoDecodeBHist D)
                                                              (realBolzanoDecodeBHist J)
                                                              (realBolzanoDecodeBHist R)
                                                              (realBolzanoDecodeBHist E)
                                                              (realBolzanoDecodeBHist H)
                                                              (realBolzanoDecodeBHist C)
                                                              (realBolzanoDecodeBHist P)
                                                              (realBolzanoDecodeBHist N))
                                                      | _ :: _ => none

private theorem RealBolzanoTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealBolzanoUp, realBolzanoFromEventFlow (realBolzanoToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk a b L U S D J R E H C P N =>
      change
        some
          (RealBolzanoUp.mk
            (realBolzanoDecodeBHist (realBolzanoEncodeBHist a))
            (realBolzanoDecodeBHist (realBolzanoEncodeBHist b))
            (realBolzanoDecodeBHist (realBolzanoEncodeBHist L))
            (realBolzanoDecodeBHist (realBolzanoEncodeBHist U))
            (realBolzanoDecodeBHist (realBolzanoEncodeBHist S))
            (realBolzanoDecodeBHist (realBolzanoEncodeBHist D))
            (realBolzanoDecodeBHist (realBolzanoEncodeBHist J))
            (realBolzanoDecodeBHist (realBolzanoEncodeBHist R))
            (realBolzanoDecodeBHist (realBolzanoEncodeBHist E))
            (realBolzanoDecodeBHist (realBolzanoEncodeBHist H))
            (realBolzanoDecodeBHist (realBolzanoEncodeBHist C))
            (realBolzanoDecodeBHist (realBolzanoEncodeBHist P))
            (realBolzanoDecodeBHist (realBolzanoEncodeBHist N))) =
          some (RealBolzanoUp.mk a b L U S D J R E H C P N)
      rw [RealBolzanoTasteGate_single_carrier_alignment_decode_encode a,
        RealBolzanoTasteGate_single_carrier_alignment_decode_encode b,
        RealBolzanoTasteGate_single_carrier_alignment_decode_encode L,
        RealBolzanoTasteGate_single_carrier_alignment_decode_encode U,
        RealBolzanoTasteGate_single_carrier_alignment_decode_encode S,
        RealBolzanoTasteGate_single_carrier_alignment_decode_encode D,
        RealBolzanoTasteGate_single_carrier_alignment_decode_encode J,
        RealBolzanoTasteGate_single_carrier_alignment_decode_encode R,
        RealBolzanoTasteGate_single_carrier_alignment_decode_encode E,
        RealBolzanoTasteGate_single_carrier_alignment_decode_encode H,
        RealBolzanoTasteGate_single_carrier_alignment_decode_encode C,
        RealBolzanoTasteGate_single_carrier_alignment_decode_encode P,
        RealBolzanoTasteGate_single_carrier_alignment_decode_encode N]

private theorem RealBolzanoTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealBolzanoUp} :
    realBolzanoToEventFlow x = realBolzanoToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realBolzanoFromEventFlow (realBolzanoToEventFlow x) =
        realBolzanoFromEventFlow (realBolzanoToEventFlow y) :=
    congrArg realBolzanoFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealBolzanoTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealBolzanoTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealBolzanoTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RealBolzanoUp, realBolzanoFields x = realBolzanoFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk a₁ b₁ L₁ U₁ S₁ D₁ J₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk a₂ b₂ L₂ U₂ S₂ D₂ J₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          injection hfields with ha tail0
          injection tail0 with hb tail1
          injection tail1 with hL tail2
          injection tail2 with hU tail3
          injection tail3 with hS tail4
          injection tail4 with hD tail5
          injection tail5 with hJ tail6
          injection tail6 with hR tail7
          injection tail7 with hE tail8
          injection tail8 with hH tail9
          injection tail9 with hC tail10
          injection tail10 with hP tail11
          injection tail11 with hN _
          subst ha
          subst hb
          subst hL
          subst hU
          subst hS
          subst hD
          subst hJ
          subst hR
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance realBolzanoBHistCarrier : BHistCarrier RealBolzanoUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realBolzanoToEventFlow
  fromEventFlow := realBolzanoFromEventFlow

instance realBolzanoChapterTasteGate : ChapterTasteGate RealBolzanoUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realBolzanoFromEventFlow (realBolzanoToEventFlow x) = some x
    exact RealBolzanoTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealBolzanoTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realBolzanoFieldFaithful : FieldFaithful RealBolzanoUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realBolzanoFields
  field_faithful := RealBolzanoTasteGate_single_carrier_alignment_fields_faithful

instance realBolzanoNontrivial : Nontrivial RealBolzanoUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealBolzanoUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealBolzanoUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RealBolzanoTasteGate_single_carrier_alignment :
    (∀ h : BHist, realBolzanoDecodeBHist (realBolzanoEncodeBHist h) = h) ∧
      (∀ x : RealBolzanoUp, realBolzanoFromEventFlow (realBolzanoToEventFlow x) = some x) ∧
        (∀ x y : RealBolzanoUp,
          realBolzanoToEventFlow x = realBolzanoToEventFlow y → x = y) ∧
          realBolzanoEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : RealBolzanoUp, realBolzanoFields x = realBolzanoFields y → x = y) ∧
              (∃ x y : RealBolzanoUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨RealBolzanoTasteGate_single_carrier_alignment_decode_encode,
      RealBolzanoTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => RealBolzanoTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl,
      RealBolzanoTasteGate_single_carrier_alignment_fields_faithful,
      ⟨RealBolzanoUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        RealBolzanoUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩⟩

end BEDC.Derived.RealBolzanoUp
