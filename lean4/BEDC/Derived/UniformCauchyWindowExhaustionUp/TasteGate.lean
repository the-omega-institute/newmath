import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformCauchyWindowExhaustionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformCauchyWindowExhaustionUp : Type where
  | mk (S T D R E H C P N : BHist) : UniformCauchyWindowExhaustionUp
  deriving DecidableEq

def uniformCauchyWindowExhaustionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformCauchyWindowExhaustionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformCauchyWindowExhaustionEncodeBHist h

def uniformCauchyWindowExhaustionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformCauchyWindowExhaustionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformCauchyWindowExhaustionDecodeBHist tail)

private theorem UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      uniformCauchyWindowExhaustionDecodeBHist
          (uniformCauchyWindowExhaustionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformCauchyWindowExhaustionFields :
    UniformCauchyWindowExhaustionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformCauchyWindowExhaustionUp.mk S T D R E H C P N => [S, T, D, R, E, H, C, P, N]

def uniformCauchyWindowExhaustionToEventFlow :
    UniformCauchyWindowExhaustionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformCauchyWindowExhaustionFields x).map uniformCauchyWindowExhaustionEncodeBHist

def uniformCauchyWindowExhaustionFromEventFlow :
    EventFlow → Option UniformCauchyWindowExhaustionUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: restS =>
      match restS with
      | T :: restT =>
          match restT with
          | D :: restD =>
              match restD with
              | R :: restR =>
                  match restR with
                  | E :: restE =>
                      match restE with
                      | H :: restH =>
                          match restH with
                          | C :: restC =>
                              match restC with
                              | P :: restP =>
                                  match restP with
                                  | N :: rest =>
                                      match rest with
                                      | [] =>
                                          some
                                            (UniformCauchyWindowExhaustionUp.mk
                                              (uniformCauchyWindowExhaustionDecodeBHist S)
                                              (uniformCauchyWindowExhaustionDecodeBHist T)
                                              (uniformCauchyWindowExhaustionDecodeBHist D)
                                              (uniformCauchyWindowExhaustionDecodeBHist R)
                                              (uniformCauchyWindowExhaustionDecodeBHist E)
                                              (uniformCauchyWindowExhaustionDecodeBHist H)
                                              (uniformCauchyWindowExhaustionDecodeBHist C)
                                              (uniformCauchyWindowExhaustionDecodeBHist P)
                                              (uniformCauchyWindowExhaustionDecodeBHist N))
                                      | _ :: _ => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UniformCauchyWindowExhaustionUp,
      uniformCauchyWindowExhaustionFromEventFlow
          (uniformCauchyWindowExhaustionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T D R E H C P N =>
      change
        some
          (UniformCauchyWindowExhaustionUp.mk
            (uniformCauchyWindowExhaustionDecodeBHist
              (uniformCauchyWindowExhaustionEncodeBHist S))
            (uniformCauchyWindowExhaustionDecodeBHist
              (uniformCauchyWindowExhaustionEncodeBHist T))
            (uniformCauchyWindowExhaustionDecodeBHist
              (uniformCauchyWindowExhaustionEncodeBHist D))
            (uniformCauchyWindowExhaustionDecodeBHist
              (uniformCauchyWindowExhaustionEncodeBHist R))
            (uniformCauchyWindowExhaustionDecodeBHist
              (uniformCauchyWindowExhaustionEncodeBHist E))
            (uniformCauchyWindowExhaustionDecodeBHist
              (uniformCauchyWindowExhaustionEncodeBHist H))
            (uniformCauchyWindowExhaustionDecodeBHist
              (uniformCauchyWindowExhaustionEncodeBHist C))
            (uniformCauchyWindowExhaustionDecodeBHist
              (uniformCauchyWindowExhaustionEncodeBHist P))
            (uniformCauchyWindowExhaustionDecodeBHist
              (uniformCauchyWindowExhaustionEncodeBHist N))) =
          some (UniformCauchyWindowExhaustionUp.mk S T D R E H C P N)
      rw [UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_decode S,
        UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_decode T,
        UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_decode D,
        UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_decode R,
        UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_decode E,
        UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_decode H,
        UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_decode C,
        UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_decode P,
        UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_decode N]

private theorem UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_injective
    {x y : UniformCauchyWindowExhaustionUp} :
    uniformCauchyWindowExhaustionToEventFlow x =
        uniformCauchyWindowExhaustionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformCauchyWindowExhaustionFromEventFlow
          (uniformCauchyWindowExhaustionToEventFlow x) =
        uniformCauchyWindowExhaustionFromEventFlow
          (uniformCauchyWindowExhaustionToEventFlow y) :=
    congrArg uniformCauchyWindowExhaustionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_round_trip y)))

private theorem UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_fields :
    ∀ x y : UniformCauchyWindowExhaustionUp,
      uniformCauchyWindowExhaustionFields x = uniformCauchyWindowExhaustionFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ T₁ D₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ T₂ D₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hS tail0
          injection tail0 with hT tail1
          injection tail1 with hD tail2
          injection tail2 with hR tail3
          injection tail3 with hE tail4
          injection tail4 with hH tail5
          injection tail5 with hC tail6
          injection tail6 with hP tail7
          injection tail7 with hN _
          subst hS
          subst hT
          subst hD
          subst hR
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance uniformCauchyWindowExhaustionBHistCarrier :
    BHistCarrier UniformCauchyWindowExhaustionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformCauchyWindowExhaustionToEventFlow
  fromEventFlow := uniformCauchyWindowExhaustionFromEventFlow

instance uniformCauchyWindowExhaustionChapterTasteGate :
    ChapterTasteGate UniformCauchyWindowExhaustionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformCauchyWindowExhaustionFromEventFlow
          (uniformCauchyWindowExhaustionToEventFlow x) =
        some x
    exact UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_injective heq)

instance uniformCauchyWindowExhaustionFieldFaithful :
    FieldFaithful UniformCauchyWindowExhaustionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformCauchyWindowExhaustionFields
  field_faithful := UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_fields

instance uniformCauchyWindowExhaustionNontrivial :
    Nontrivial UniformCauchyWindowExhaustionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformCauchyWindowExhaustionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UniformCauchyWindowExhaustionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate UniformCauchyWindowExhaustionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformCauchyWindowExhaustionChapterTasteGate

theorem UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      uniformCauchyWindowExhaustionDecodeBHist
          (uniformCauchyWindowExhaustionEncodeBHist h) =
        h) ∧
      (∀ x : UniformCauchyWindowExhaustionUp,
        uniformCauchyWindowExhaustionFromEventFlow
            (uniformCauchyWindowExhaustionToEventFlow x) =
          some x) ∧
      uniformCauchyWindowExhaustionEncodeBHist BHist.Empty = ([] : List BMark) ∧
      uniformCauchyWindowExhaustionEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
      Nonempty (ChapterTasteGate UniformCauchyWindowExhaustionUp) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_decode
  constructor
  · exact UniformCauchyWindowExhaustionTasteGate_single_carrier_alignment_round_trip
  constructor
  · rfl
  constructor
  · rfl
  · exact ⟨uniformCauchyWindowExhaustionChapterTasteGate⟩

end BEDC.Derived.UniformCauchyWindowExhaustionUp
