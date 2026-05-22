import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRateDominanceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyRateDominanceUp : Type where
  | mk (M D S Q E H C P N : BHist) : CauchyRateDominanceUp
  deriving DecidableEq

def cauchyRateDominanceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyRateDominanceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyRateDominanceEncodeBHist h

def cauchyRateDominanceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyRateDominanceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyRateDominanceDecodeBHist tail)

private theorem CauchyRateDominanceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cauchyRateDominanceDecodeBHist (cauchyRateDominanceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyRateDominanceFields : CauchyRateDominanceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRateDominanceUp.mk M D S Q E H C P N => [M, D, S, Q, E, H, C, P, N]

def cauchyRateDominanceToEventFlow : CauchyRateDominanceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyRateDominanceFields x).map cauchyRateDominanceEncodeBHist

def cauchyRateDominanceFromEventFlow : EventFlow → Option CauchyRateDominanceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | M :: restM =>
      match restM with
      | [] => none
      | D :: restD =>
          match restD with
          | [] => none
          | S :: restS =>
              match restS with
              | [] => none
              | Q :: restQ =>
                  match restQ with
                  | [] => none
                  | E :: restE =>
                      match restE with
                      | [] => none
                      | H :: restH =>
                          match restH with
                          | [] => none
                          | C :: restC =>
                              match restC with
                              | [] => none
                              | P :: restP =>
                                  match restP with
                                  | [] => none
                                  | N :: restN =>
                                      match restN with
                                      | [] =>
                                          some
                                            (CauchyRateDominanceUp.mk
                                              (cauchyRateDominanceDecodeBHist M)
                                              (cauchyRateDominanceDecodeBHist D)
                                              (cauchyRateDominanceDecodeBHist S)
                                              (cauchyRateDominanceDecodeBHist Q)
                                              (cauchyRateDominanceDecodeBHist E)
                                              (cauchyRateDominanceDecodeBHist H)
                                              (cauchyRateDominanceDecodeBHist C)
                                              (cauchyRateDominanceDecodeBHist P)
                                              (cauchyRateDominanceDecodeBHist N))
                                      | _ :: _ => none

private theorem CauchyRateDominanceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyRateDominanceUp,
      cauchyRateDominanceFromEventFlow (cauchyRateDominanceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M D S Q E H C P N =>
      change
        some
          (CauchyRateDominanceUp.mk
            (cauchyRateDominanceDecodeBHist (cauchyRateDominanceEncodeBHist M))
            (cauchyRateDominanceDecodeBHist (cauchyRateDominanceEncodeBHist D))
            (cauchyRateDominanceDecodeBHist (cauchyRateDominanceEncodeBHist S))
            (cauchyRateDominanceDecodeBHist (cauchyRateDominanceEncodeBHist Q))
            (cauchyRateDominanceDecodeBHist (cauchyRateDominanceEncodeBHist E))
            (cauchyRateDominanceDecodeBHist (cauchyRateDominanceEncodeBHist H))
            (cauchyRateDominanceDecodeBHist (cauchyRateDominanceEncodeBHist C))
            (cauchyRateDominanceDecodeBHist (cauchyRateDominanceEncodeBHist P))
            (cauchyRateDominanceDecodeBHist (cauchyRateDominanceEncodeBHist N))) =
          some (CauchyRateDominanceUp.mk M D S Q E H C P N)
      rw [CauchyRateDominanceTasteGate_single_carrier_alignment_decode_encode M,
        CauchyRateDominanceTasteGate_single_carrier_alignment_decode_encode D,
        CauchyRateDominanceTasteGate_single_carrier_alignment_decode_encode S,
        CauchyRateDominanceTasteGate_single_carrier_alignment_decode_encode Q,
        CauchyRateDominanceTasteGate_single_carrier_alignment_decode_encode E,
        CauchyRateDominanceTasteGate_single_carrier_alignment_decode_encode H,
        CauchyRateDominanceTasteGate_single_carrier_alignment_decode_encode C,
        CauchyRateDominanceTasteGate_single_carrier_alignment_decode_encode P,
        CauchyRateDominanceTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyRateDominanceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyRateDominanceUp} :
    cauchyRateDominanceToEventFlow x = cauchyRateDominanceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyRateDominanceFromEventFlow (cauchyRateDominanceToEventFlow x) =
        cauchyRateDominanceFromEventFlow (cauchyRateDominanceToEventFlow y) :=
    congrArg cauchyRateDominanceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyRateDominanceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyRateDominanceTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyRateDominanceTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : CauchyRateDominanceUp,
      cauchyRateDominanceFields x = cauchyRateDominanceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ D₁ S₁ Q₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk M₂ D₂ S₂ Q₂ E₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hM tailD
          injection tailD with hD tailS
          injection tailS with hS tailQ
          injection tailQ with hQ tailE
          injection tailE with hE tailH
          injection tailH with hH tailC
          injection tailC with hC tailP
          injection tailP with hP tailN
          injection tailN with hN _
          subst hM
          subst hD
          subst hS
          subst hQ
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance cauchyRateDominanceBHistCarrier : BHistCarrier CauchyRateDominanceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyRateDominanceToEventFlow
  fromEventFlow := cauchyRateDominanceFromEventFlow

instance cauchyRateDominanceChapterTasteGate : ChapterTasteGate CauchyRateDominanceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyRateDominanceFromEventFlow (cauchyRateDominanceToEventFlow x) = some x
    exact CauchyRateDominanceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyRateDominanceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyRateDominanceFieldFaithful : FieldFaithful CauchyRateDominanceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyRateDominanceFields
  field_faithful := CauchyRateDominanceTasteGate_single_carrier_alignment_field_faithful

instance cauchyRateDominanceNontrivial : Nontrivial CauchyRateDominanceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyRateDominanceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyRateDominanceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyRateDominanceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyRateDominanceChapterTasteGate

theorem CauchyRateDominanceTasteGate_single_carrier_alignment :
    ChapterTasteGate CauchyRateDominanceUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact inferInstance

end BEDC.Derived.CauchyRateDominanceUp.TasteGate
