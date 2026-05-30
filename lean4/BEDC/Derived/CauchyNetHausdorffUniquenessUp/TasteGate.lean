import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyNetHausdorffUniquenessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyNetHausdorffUniquenessUp : Type where
  | mk (D L0 L1 S M H C P N : BHist) : CauchyNetHausdorffUniquenessUp
  deriving DecidableEq

def cauchyNetHausdorffUniquenessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyNetHausdorffUniquenessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyNetHausdorffUniquenessEncodeBHist h

def cauchyNetHausdorffUniquenessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyNetHausdorffUniquenessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyNetHausdorffUniquenessDecodeBHist tail)

private theorem CauchyNetHausdorffUniquenessTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyNetHausdorffUniquenessDecodeBHist
          (cauchyNetHausdorffUniquenessEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyNetHausdorffUniquenessFields :
    CauchyNetHausdorffUniquenessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyNetHausdorffUniquenessUp.mk D L0 L1 S M H C P N =>
      [D, L0, L1, S, M, H, C, P, N]

def cauchyNetHausdorffUniquenessToEventFlow :
    CauchyNetHausdorffUniquenessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      [BMark.b0, BMark.b1, BMark.b0] ::
        (cauchyNetHausdorffUniquenessFields x).map
          cauchyNetHausdorffUniquenessEncodeBHist

def cauchyNetHausdorffUniquenessFromEventFlow :
    EventFlow → Option CauchyNetHausdorffUniquenessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: restD =>
      match restD with
      | [] => none
      | D :: restL0 =>
          match restL0 with
          | [] => none
          | L0 :: restL1 =>
              match restL1 with
              | [] => none
              | L1 :: restS =>
                  match restS with
                  | [] => none
                  | S :: restM =>
                      match restM with
                      | [] => none
                      | M :: restH =>
                          match restH with
                          | [] => none
                          | H :: restC =>
                              match restC with
                              | [] => none
                              | C :: restP =>
                                  match restP with
                                  | [] => none
                                  | P :: restN =>
                                      match restN with
                                      | [] => none
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (CauchyNetHausdorffUniquenessUp.mk
                                                  (cauchyNetHausdorffUniquenessDecodeBHist D)
                                                  (cauchyNetHausdorffUniquenessDecodeBHist L0)
                                                  (cauchyNetHausdorffUniquenessDecodeBHist L1)
                                                  (cauchyNetHausdorffUniquenessDecodeBHist S)
                                                  (cauchyNetHausdorffUniquenessDecodeBHist M)
                                                  (cauchyNetHausdorffUniquenessDecodeBHist H)
                                                  (cauchyNetHausdorffUniquenessDecodeBHist C)
                                                  (cauchyNetHausdorffUniquenessDecodeBHist P)
                                                  (cauchyNetHausdorffUniquenessDecodeBHist N))
                                          | _ :: _ => none

private theorem CauchyNetHausdorffUniquenessTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyNetHausdorffUniquenessUp,
      cauchyNetHausdorffUniquenessFromEventFlow
          (cauchyNetHausdorffUniquenessToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D L0 L1 S M H C P N =>
      change
        some
          (CauchyNetHausdorffUniquenessUp.mk
            (cauchyNetHausdorffUniquenessDecodeBHist
              (cauchyNetHausdorffUniquenessEncodeBHist D))
            (cauchyNetHausdorffUniquenessDecodeBHist
              (cauchyNetHausdorffUniquenessEncodeBHist L0))
            (cauchyNetHausdorffUniquenessDecodeBHist
              (cauchyNetHausdorffUniquenessEncodeBHist L1))
            (cauchyNetHausdorffUniquenessDecodeBHist
              (cauchyNetHausdorffUniquenessEncodeBHist S))
            (cauchyNetHausdorffUniquenessDecodeBHist
              (cauchyNetHausdorffUniquenessEncodeBHist M))
            (cauchyNetHausdorffUniquenessDecodeBHist
              (cauchyNetHausdorffUniquenessEncodeBHist H))
            (cauchyNetHausdorffUniquenessDecodeBHist
              (cauchyNetHausdorffUniquenessEncodeBHist C))
            (cauchyNetHausdorffUniquenessDecodeBHist
              (cauchyNetHausdorffUniquenessEncodeBHist P))
            (cauchyNetHausdorffUniquenessDecodeBHist
              (cauchyNetHausdorffUniquenessEncodeBHist N))) =
          some (CauchyNetHausdorffUniquenessUp.mk D L0 L1 S M H C P N)
      rw [CauchyNetHausdorffUniquenessTasteGate_single_carrier_alignment_decode_encode D,
        CauchyNetHausdorffUniquenessTasteGate_single_carrier_alignment_decode_encode L0,
        CauchyNetHausdorffUniquenessTasteGate_single_carrier_alignment_decode_encode L1,
        CauchyNetHausdorffUniquenessTasteGate_single_carrier_alignment_decode_encode S,
        CauchyNetHausdorffUniquenessTasteGate_single_carrier_alignment_decode_encode M,
        CauchyNetHausdorffUniquenessTasteGate_single_carrier_alignment_decode_encode H,
        CauchyNetHausdorffUniquenessTasteGate_single_carrier_alignment_decode_encode C,
        CauchyNetHausdorffUniquenessTasteGate_single_carrier_alignment_decode_encode P,
        CauchyNetHausdorffUniquenessTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyNetHausdorffUniquenessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyNetHausdorffUniquenessUp} :
    cauchyNetHausdorffUniquenessToEventFlow x =
      cauchyNetHausdorffUniquenessToEventFlow y →
    x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyNetHausdorffUniquenessFromEventFlow
          (cauchyNetHausdorffUniquenessToEventFlow x) =
        cauchyNetHausdorffUniquenessFromEventFlow
          (cauchyNetHausdorffUniquenessToEventFlow y) :=
    congrArg cauchyNetHausdorffUniquenessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyNetHausdorffUniquenessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyNetHausdorffUniquenessTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyNetHausdorffUniquenessTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CauchyNetHausdorffUniquenessUp,
      cauchyNetHausdorffUniquenessFields x =
        cauchyNetHausdorffUniquenessFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D₁ L0₁ L1₁ S₁ M₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk D₂ L0₂ L1₂ S₂ M₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hD tail1
          injection tail1 with hL0 tail2
          injection tail2 with hL1 tail3
          injection tail3 with hS tail4
          injection tail4 with hM tail5
          injection tail5 with hH tail6
          injection tail6 with hC tail7
          injection tail7 with hP tail8
          injection tail8 with hN _
          subst hD
          subst hL0
          subst hL1
          subst hS
          subst hM
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance cauchyNetHausdorffUniquenessBHistCarrier :
    BHistCarrier CauchyNetHausdorffUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyNetHausdorffUniquenessToEventFlow
  fromEventFlow := cauchyNetHausdorffUniquenessFromEventFlow

instance cauchyNetHausdorffUniquenessChapterTasteGate :
    ChapterTasteGate CauchyNetHausdorffUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyNetHausdorffUniquenessFromEventFlow
          (cauchyNetHausdorffUniquenessToEventFlow x) =
        some x
    exact CauchyNetHausdorffUniquenessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyNetHausdorffUniquenessTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance cauchyNetHausdorffUniquenessFieldFaithful :
    FieldFaithful CauchyNetHausdorffUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyNetHausdorffUniquenessFields
  field_faithful :=
    CauchyNetHausdorffUniquenessTasteGate_single_carrier_alignment_fields_faithful

instance cauchyNetHausdorffUniquenessNontrivial :
    Nontrivial CauchyNetHausdorffUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyNetHausdorffUniquenessUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyNetHausdorffUniquenessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        injection h with hD
        cases hD⟩

def taste_gate : ChapterTasteGate CauchyNetHausdorffUniquenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyNetHausdorffUniquenessChapterTasteGate

theorem CauchyNetHausdorffUniquenessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyNetHausdorffUniquenessDecodeBHist
          (cauchyNetHausdorffUniquenessEncodeBHist h) =
        h) ∧
      (∀ x : CauchyNetHausdorffUniquenessUp,
        cauchyNetHausdorffUniquenessFromEventFlow
            (cauchyNetHausdorffUniquenessToEventFlow x) =
          some x) ∧
        (∀ x y : CauchyNetHausdorffUniquenessUp,
          cauchyNetHausdorffUniquenessToEventFlow x =
            cauchyNetHausdorffUniquenessToEventFlow y →
          x = y) ∧
          cauchyNetHausdorffUniquenessFields
              (CauchyNetHausdorffUniquenessUp.mk BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty) =
            [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
              BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] ∧
            cauchyNetHausdorffUniquenessEncodeBHist BHist.Empty =
              ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨CauchyNetHausdorffUniquenessTasteGate_single_carrier_alignment_decode_encode,
      CauchyNetHausdorffUniquenessTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        CauchyNetHausdorffUniquenessTasteGate_single_carrier_alignment_toEventFlow_injective
          heq,
      rfl,
      rfl⟩

end BEDC.Derived.CauchyNetHausdorffUniquenessUp
