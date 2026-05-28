import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformEntourageSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformEntourageSpaceUp : Type where
  | mk (E D S R C L T K P N : BHist) : UniformEntourageSpaceUp
  deriving DecidableEq

def uniformEntourageSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformEntourageSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformEntourageSpaceEncodeBHist h

def uniformEntourageSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformEntourageSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformEntourageSpaceDecodeBHist tail)

private theorem UniformEntourageSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      uniformEntourageSpaceDecodeBHist (uniformEntourageSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def uniformEntourageSpaceFields : UniformEntourageSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformEntourageSpaceUp.mk E D S R C L T K P N =>
      [E, D, S, R, C, L, T, K, P, N]

def uniformEntourageSpaceToEventFlow : UniformEntourageSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      [BMark.b1, BMark.b0, BMark.b1] ::
        (uniformEntourageSpaceFields x).map uniformEntourageSpaceEncodeBHist

def uniformEntourageSpaceFromEventFlow :
    EventFlow → Option UniformEntourageSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: restE =>
      match restE with
      | [] => none
      | E :: restD =>
          match restD with
          | [] => none
          | D :: restS =>
              match restS with
              | [] => none
              | S :: restR =>
                  match restR with
                  | [] => none
                  | R :: restC =>
                      match restC with
                      | [] => none
                      | C :: restL =>
                          match restL with
                          | [] => none
                          | L :: restT =>
                              match restT with
                              | [] => none
                              | T :: restK =>
                                  match restK with
                                  | [] => none
                                  | K :: restP =>
                                      match restP with
                                      | [] => none
                                      | P :: restN =>
                                          match restN with
                                          | [] => none
                                          | N :: rest =>
                                              match rest with
                                              | [] =>
                                                  some
                                                    (UniformEntourageSpaceUp.mk
                                                      (uniformEntourageSpaceDecodeBHist E)
                                                      (uniformEntourageSpaceDecodeBHist D)
                                                      (uniformEntourageSpaceDecodeBHist S)
                                                      (uniformEntourageSpaceDecodeBHist R)
                                                      (uniformEntourageSpaceDecodeBHist C)
                                                      (uniformEntourageSpaceDecodeBHist L)
                                                      (uniformEntourageSpaceDecodeBHist T)
                                                      (uniformEntourageSpaceDecodeBHist K)
                                                      (uniformEntourageSpaceDecodeBHist P)
                                                      (uniformEntourageSpaceDecodeBHist N))
                                              | _ :: _ => none

private theorem UniformEntourageSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UniformEntourageSpaceUp,
      uniformEntourageSpaceFromEventFlow (uniformEntourageSpaceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E D S R C L T K P N =>
      change
        some
          (UniformEntourageSpaceUp.mk
            (uniformEntourageSpaceDecodeBHist
              (uniformEntourageSpaceEncodeBHist E))
            (uniformEntourageSpaceDecodeBHist
              (uniformEntourageSpaceEncodeBHist D))
            (uniformEntourageSpaceDecodeBHist
              (uniformEntourageSpaceEncodeBHist S))
            (uniformEntourageSpaceDecodeBHist
              (uniformEntourageSpaceEncodeBHist R))
            (uniformEntourageSpaceDecodeBHist
              (uniformEntourageSpaceEncodeBHist C))
            (uniformEntourageSpaceDecodeBHist
              (uniformEntourageSpaceEncodeBHist L))
            (uniformEntourageSpaceDecodeBHist
              (uniformEntourageSpaceEncodeBHist T))
            (uniformEntourageSpaceDecodeBHist
              (uniformEntourageSpaceEncodeBHist K))
            (uniformEntourageSpaceDecodeBHist
              (uniformEntourageSpaceEncodeBHist P))
            (uniformEntourageSpaceDecodeBHist
              (uniformEntourageSpaceEncodeBHist N))) =
          some (UniformEntourageSpaceUp.mk E D S R C L T K P N)
      rw [UniformEntourageSpaceTasteGate_single_carrier_alignment_decode_encode E,
        UniformEntourageSpaceTasteGate_single_carrier_alignment_decode_encode D,
        UniformEntourageSpaceTasteGate_single_carrier_alignment_decode_encode S,
        UniformEntourageSpaceTasteGate_single_carrier_alignment_decode_encode R,
        UniformEntourageSpaceTasteGate_single_carrier_alignment_decode_encode C,
        UniformEntourageSpaceTasteGate_single_carrier_alignment_decode_encode L,
        UniformEntourageSpaceTasteGate_single_carrier_alignment_decode_encode T,
        UniformEntourageSpaceTasteGate_single_carrier_alignment_decode_encode K,
        UniformEntourageSpaceTasteGate_single_carrier_alignment_decode_encode P,
        UniformEntourageSpaceTasteGate_single_carrier_alignment_decode_encode N]

private theorem UniformEntourageSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformEntourageSpaceUp} :
    uniformEntourageSpaceToEventFlow x = uniformEntourageSpaceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformEntourageSpaceFromEventFlow (uniformEntourageSpaceToEventFlow x) =
        uniformEntourageSpaceFromEventFlow (uniformEntourageSpaceToEventFlow y) :=
    congrArg uniformEntourageSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (UniformEntourageSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (UniformEntourageSpaceTasteGate_single_carrier_alignment_round_trip y)))

private theorem UniformEntourageSpaceTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : UniformEntourageSpaceUp,
      uniformEntourageSpaceFields x = uniformEntourageSpaceFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk E₁ D₁ S₁ R₁ C₁ L₁ T₁ K₁ P₁ N₁ =>
      cases y with
      | mk E₂ D₂ S₂ R₂ C₂ L₂ T₂ K₂ P₂ N₂ =>
          injection hfields with hE tail1
          injection tail1 with hD tail2
          injection tail2 with hS tail3
          injection tail3 with hR tail4
          injection tail4 with hC tail5
          injection tail5 with hL tail6
          injection tail6 with hT tail7
          injection tail7 with hK tail8
          injection tail8 with hP tail9
          injection tail9 with hN _
          subst hE
          subst hD
          subst hS
          subst hR
          subst hC
          subst hL
          subst hT
          subst hK
          subst hP
          subst hN
          rfl

instance uniformEntourageSpaceBHistCarrier :
    BHistCarrier UniformEntourageSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformEntourageSpaceToEventFlow
  fromEventFlow := uniformEntourageSpaceFromEventFlow

instance uniformEntourageSpaceChapterTasteGate :
    ChapterTasteGate UniformEntourageSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformEntourageSpaceFromEventFlow (uniformEntourageSpaceToEventFlow x) =
        some x
    exact UniformEntourageSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (UniformEntourageSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance uniformEntourageSpaceFieldFaithful :
    FieldFaithful UniformEntourageSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformEntourageSpaceFields
  field_faithful :=
    UniformEntourageSpaceTasteGate_single_carrier_alignment_fields_faithful

instance uniformEntourageSpaceNontrivial :
    Nontrivial UniformEntourageSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformEntourageSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UniformEntourageSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        injection h with hE
        cases hE⟩

def taste_gate : ChapterTasteGate UniformEntourageSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformEntourageSpaceChapterTasteGate

theorem UniformEntourageSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      uniformEntourageSpaceDecodeBHist
          (uniformEntourageSpaceEncodeBHist h) =
        h) ∧
      (∀ x : UniformEntourageSpaceUp,
        uniformEntourageSpaceFromEventFlow
            (uniformEntourageSpaceToEventFlow x) =
          some x) ∧
        (∀ x y : UniformEntourageSpaceUp,
          uniformEntourageSpaceToEventFlow x =
            uniformEntourageSpaceToEventFlow y →
          x = y) ∧
          uniformEntourageSpaceFields
              (UniformEntourageSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty) =
            [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
              BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] ∧
            uniformEntourageSpaceEncodeBHist BHist.Empty =
              ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨UniformEntourageSpaceTasteGate_single_carrier_alignment_decode_encode,
      UniformEntourageSpaceTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        UniformEntourageSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl,
      rfl⟩

end BEDC.Derived.UniformEntourageSpaceUp
