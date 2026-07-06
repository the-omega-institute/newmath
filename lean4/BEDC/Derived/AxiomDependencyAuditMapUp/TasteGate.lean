import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AxiomDependencyAuditMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AxiomDependencyAuditMapUp : Type where
  | mk : (K M W A L H C P N : BHist) → AxiomDependencyAuditMapUp
  deriving DecidableEq

def axiomDependencyAuditMapEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: axiomDependencyAuditMapEncodeBHist h
  | BHist.e1 h => BMark.b1 :: axiomDependencyAuditMapEncodeBHist h

def axiomDependencyAuditMapDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (axiomDependencyAuditMapDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (axiomDependencyAuditMapDecodeBHist tail)

private theorem AxiomDependencyAuditMapTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, axiomDependencyAuditMapDecodeBHist (axiomDependencyAuditMapEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def axiomDependencyAuditMapFields : AxiomDependencyAuditMapUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AxiomDependencyAuditMapUp.mk K M W A L H C P N => [K, M, W, A, L, H, C, P, N]

def axiomDependencyAuditMapToEventFlow : AxiomDependencyAuditMapUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (axiomDependencyAuditMapFields x).map axiomDependencyAuditMapEncodeBHist

def axiomDependencyAuditMapFromEventFlow : EventFlow → Option AxiomDependencyAuditMapUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | K :: rest0 =>
      match rest0 with
      | [] => none
      | M :: rest1 =>
          match rest1 with
          | [] => none
          | W :: rest2 =>
              match rest2 with
              | [] => none
              | A :: rest3 =>
                  match rest3 with
                  | [] => none
                  | L :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | C :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (AxiomDependencyAuditMapUp.mk
                                              (axiomDependencyAuditMapDecodeBHist K)
                                              (axiomDependencyAuditMapDecodeBHist M)
                                              (axiomDependencyAuditMapDecodeBHist W)
                                              (axiomDependencyAuditMapDecodeBHist A)
                                              (axiomDependencyAuditMapDecodeBHist L)
                                              (axiomDependencyAuditMapDecodeBHist H)
                                              (axiomDependencyAuditMapDecodeBHist C)
                                              (axiomDependencyAuditMapDecodeBHist P)
                                              (axiomDependencyAuditMapDecodeBHist N))
                                      | _ :: _ => none

private theorem AxiomDependencyAuditMapTasteGate_single_carrier_alignment_round_trip :
    ∀ x : AxiomDependencyAuditMapUp,
      axiomDependencyAuditMapFromEventFlow (axiomDependencyAuditMapToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K M W A L H C P N =>
      change
        some
          (AxiomDependencyAuditMapUp.mk
            (axiomDependencyAuditMapDecodeBHist (axiomDependencyAuditMapEncodeBHist K))
            (axiomDependencyAuditMapDecodeBHist (axiomDependencyAuditMapEncodeBHist M))
            (axiomDependencyAuditMapDecodeBHist (axiomDependencyAuditMapEncodeBHist W))
            (axiomDependencyAuditMapDecodeBHist (axiomDependencyAuditMapEncodeBHist A))
            (axiomDependencyAuditMapDecodeBHist (axiomDependencyAuditMapEncodeBHist L))
            (axiomDependencyAuditMapDecodeBHist (axiomDependencyAuditMapEncodeBHist H))
            (axiomDependencyAuditMapDecodeBHist (axiomDependencyAuditMapEncodeBHist C))
            (axiomDependencyAuditMapDecodeBHist (axiomDependencyAuditMapEncodeBHist P))
            (axiomDependencyAuditMapDecodeBHist (axiomDependencyAuditMapEncodeBHist N))) =
          some (AxiomDependencyAuditMapUp.mk K M W A L H C P N)
      rw [AxiomDependencyAuditMapTasteGate_single_carrier_alignment_decode_encode K,
        AxiomDependencyAuditMapTasteGate_single_carrier_alignment_decode_encode M,
        AxiomDependencyAuditMapTasteGate_single_carrier_alignment_decode_encode W,
        AxiomDependencyAuditMapTasteGate_single_carrier_alignment_decode_encode A,
        AxiomDependencyAuditMapTasteGate_single_carrier_alignment_decode_encode L,
        AxiomDependencyAuditMapTasteGate_single_carrier_alignment_decode_encode H,
        AxiomDependencyAuditMapTasteGate_single_carrier_alignment_decode_encode C,
        AxiomDependencyAuditMapTasteGate_single_carrier_alignment_decode_encode P,
        AxiomDependencyAuditMapTasteGate_single_carrier_alignment_decode_encode N]

private theorem AxiomDependencyAuditMapTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AxiomDependencyAuditMapUp} :
    axiomDependencyAuditMapToEventFlow x = axiomDependencyAuditMapToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      axiomDependencyAuditMapFromEventFlow (axiomDependencyAuditMapToEventFlow x) =
        axiomDependencyAuditMapFromEventFlow (axiomDependencyAuditMapToEventFlow y) :=
    congrArg axiomDependencyAuditMapFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (AxiomDependencyAuditMapTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (AxiomDependencyAuditMapTasteGate_single_carrier_alignment_round_trip y)))

private theorem AxiomDependencyAuditMapTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : AxiomDependencyAuditMapUp,
      axiomDependencyAuditMapFields x = axiomDependencyAuditMapFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K₁ M₁ W₁ A₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ M₂ W₂ A₂ L₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hK tail0
          injection tail0 with hM tail1
          injection tail1 with hW tail2
          injection tail2 with hA tail3
          injection tail3 with hL tail4
          injection tail4 with hH tail5
          injection tail5 with hC tail6
          injection tail6 with hP tail7
          injection tail7 with hN _
          subst hK
          subst hM
          subst hW
          subst hA
          subst hL
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance axiomDependencyAuditMapBHistCarrier : BHistCarrier AxiomDependencyAuditMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := axiomDependencyAuditMapToEventFlow
  fromEventFlow := axiomDependencyAuditMapFromEventFlow

instance axiomDependencyAuditMapChapterTasteGate :
    ChapterTasteGate AxiomDependencyAuditMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change axiomDependencyAuditMapFromEventFlow (axiomDependencyAuditMapToEventFlow x) = some x
    exact AxiomDependencyAuditMapTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AxiomDependencyAuditMapTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance axiomDependencyAuditMapFieldFaithful : FieldFaithful AxiomDependencyAuditMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := axiomDependencyAuditMapFields
  field_faithful := AxiomDependencyAuditMapTasteGate_single_carrier_alignment_fields_faithful

instance axiomDependencyAuditMapNontrivial : Nontrivial AxiomDependencyAuditMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AxiomDependencyAuditMapUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AxiomDependencyAuditMapUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AxiomDependencyAuditMapUp :=
  -- BEDC touchpoint anchor: BHist BMark
  axiomDependencyAuditMapChapterTasteGate

theorem AxiomDependencyAuditMapTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate AxiomDependencyAuditMapUp) ∧
      Nonempty (FieldFaithful AxiomDependencyAuditMapUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial AxiomDependencyAuditMapUp) ∧
          (∀ h : BHist,
            axiomDependencyAuditMapDecodeBHist (axiomDependencyAuditMapEncodeBHist h) = h) ∧
            (∀ x : AxiomDependencyAuditMapUp,
              axiomDependencyAuditMapFromEventFlow (axiomDependencyAuditMapToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨axiomDependencyAuditMapChapterTasteGate⟩,
      ⟨⟨axiomDependencyAuditMapFieldFaithful⟩,
        ⟨⟨axiomDependencyAuditMapNontrivial⟩,
          AxiomDependencyAuditMapTasteGate_single_carrier_alignment_decode_encode,
          AxiomDependencyAuditMapTasteGate_single_carrier_alignment_round_trip⟩⟩⟩

end BEDC.Derived.AxiomDependencyAuditMapUp
