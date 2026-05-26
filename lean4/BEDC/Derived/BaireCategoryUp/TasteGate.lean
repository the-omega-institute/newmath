import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BaireCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BaireCategoryUp : Type where
  | mk (B M D O R T H C P N : BHist) : BaireCategoryUp
  deriving DecidableEq

def baireCategoryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: baireCategoryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: baireCategoryEncodeBHist h

def baireCategoryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (baireCategoryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (baireCategoryDecodeBHist tail)

private theorem BaireCategoryTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, baireCategoryDecodeBHist (baireCategoryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def baireCategoryFields : BaireCategoryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BaireCategoryUp.mk B M D O R T H C P N => [B, M, D, O, R, T, H, C, P, N]

def baireCategoryToEventFlow : BaireCategoryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (baireCategoryFields x).map baireCategoryEncodeBHist

private def baireCategoryEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => baireCategoryEventAt index rest

def baireCategoryFromEventFlow (ef : EventFlow) : Option BaireCategoryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BaireCategoryUp.mk
      (baireCategoryDecodeBHist (baireCategoryEventAt 0 ef))
      (baireCategoryDecodeBHist (baireCategoryEventAt 1 ef))
      (baireCategoryDecodeBHist (baireCategoryEventAt 2 ef))
      (baireCategoryDecodeBHist (baireCategoryEventAt 3 ef))
      (baireCategoryDecodeBHist (baireCategoryEventAt 4 ef))
      (baireCategoryDecodeBHist (baireCategoryEventAt 5 ef))
      (baireCategoryDecodeBHist (baireCategoryEventAt 6 ef))
      (baireCategoryDecodeBHist (baireCategoryEventAt 7 ef))
      (baireCategoryDecodeBHist (baireCategoryEventAt 8 ef))
      (baireCategoryDecodeBHist (baireCategoryEventAt 9 ef)))

private theorem BaireCategoryTasteGate_single_carrier_alignment_round_trip
    (x : BaireCategoryUp) :
    baireCategoryFromEventFlow (baireCategoryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B M D O R T H C P N =>
      change
        some
          (BaireCategoryUp.mk
            (baireCategoryDecodeBHist (baireCategoryEncodeBHist B))
            (baireCategoryDecodeBHist (baireCategoryEncodeBHist M))
            (baireCategoryDecodeBHist (baireCategoryEncodeBHist D))
            (baireCategoryDecodeBHist (baireCategoryEncodeBHist O))
            (baireCategoryDecodeBHist (baireCategoryEncodeBHist R))
            (baireCategoryDecodeBHist (baireCategoryEncodeBHist T))
            (baireCategoryDecodeBHist (baireCategoryEncodeBHist H))
            (baireCategoryDecodeBHist (baireCategoryEncodeBHist C))
            (baireCategoryDecodeBHist (baireCategoryEncodeBHist P))
            (baireCategoryDecodeBHist (baireCategoryEncodeBHist N))) =
          some (BaireCategoryUp.mk B M D O R T H C P N)
      rw [BaireCategoryTasteGate_single_carrier_alignment_decode_encode B,
        BaireCategoryTasteGate_single_carrier_alignment_decode_encode M,
        BaireCategoryTasteGate_single_carrier_alignment_decode_encode D,
        BaireCategoryTasteGate_single_carrier_alignment_decode_encode O,
        BaireCategoryTasteGate_single_carrier_alignment_decode_encode R,
        BaireCategoryTasteGate_single_carrier_alignment_decode_encode T,
        BaireCategoryTasteGate_single_carrier_alignment_decode_encode H,
        BaireCategoryTasteGate_single_carrier_alignment_decode_encode C,
        BaireCategoryTasteGate_single_carrier_alignment_decode_encode P,
        BaireCategoryTasteGate_single_carrier_alignment_decode_encode N]

private theorem BaireCategoryTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BaireCategoryUp} :
    baireCategoryToEventFlow x = baireCategoryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      baireCategoryFromEventFlow (baireCategoryToEventFlow x) =
        baireCategoryFromEventFlow (baireCategoryToEventFlow y) :=
    congrArg baireCategoryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BaireCategoryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BaireCategoryTasteGate_single_carrier_alignment_round_trip y)))

private theorem BaireCategoryTasteGate_single_carrier_alignment_fields :
    ∀ x y : BaireCategoryUp, baireCategoryFields x = baireCategoryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B₁ M₁ D₁ O₁ R₁ T₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk B₂ M₂ D₂ O₂ R₂ T₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance baireCategoryBHistCarrier : BHistCarrier BaireCategoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := baireCategoryToEventFlow
  fromEventFlow := baireCategoryFromEventFlow

instance baireCategoryChapterTasteGate : ChapterTasteGate BaireCategoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change baireCategoryFromEventFlow (baireCategoryToEventFlow x) = some x
    exact BaireCategoryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BaireCategoryTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance baireCategoryFieldFaithful : FieldFaithful BaireCategoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := baireCategoryFields
  field_faithful := BaireCategoryTasteGate_single_carrier_alignment_fields

instance baireCategoryNontrivial : Nontrivial BaireCategoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BaireCategoryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BaireCategoryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def BaireCategoryTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate BaireCategoryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  baireCategoryChapterTasteGate

theorem BaireCategoryTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier BaireCategoryUp) ∧
      Nonempty (ChapterTasteGate BaireCategoryUp) ∧
        (∀ h : BHist,
          baireCategoryDecodeBHist (baireCategoryEncodeBHist h) = h) ∧
          baireCategoryEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨baireCategoryBHistCarrier⟩, ⟨baireCategoryChapterTasteGate⟩,
      BaireCategoryTasteGate_single_carrier_alignment_decode_encode, rfl⟩

theorem BaireCategoryCompleteMetricObligationSurface [AskSetup] [PackageSetup]
    {B M D O R T H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M →
      PkgSig bundle P pkg →
        baireCategoryFields (BaireCategoryUp.mk B M D O R T H C P N) =
            [B, M, D, O, R, T, H, C, P, N] ∧
          SemanticNameCert
              (fun row : BHist => hsame row M ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row B ∨ hsame row M ∨ hsame row D ∨ hsame row O ∨
                  hsame row R ∨ hsame row T ∨ hsame row H ∨ hsame row C ∨
                    hsame row P ∨ hsame row N)
              (fun row : BHist => PkgSig bundle P pkg ∧ (hsame row M ∨ hsame row T))
              hsame ∧
            Nonempty (ChapterTasteGate BaireCategoryUp) := by
  -- BEDC touchpoint anchor: BHist hsame ProbeBundle PkgSig SemanticNameCert ChapterTasteGate
  intro metricUnary packageP
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row M ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row M ∨ hsame row D ∨ hsame row O ∨
              hsame row R ∨ hsame row T ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N)
          (fun row : BHist => PkgSig bundle P pkg ∧ (hsame row M ∨ hsame row T))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro M ⟨hsame_refl M, metricUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inl source.left)
    ledger_sound := by
      intro _row source
      exact ⟨packageP, Or.inl source.left⟩
  }
  exact ⟨rfl, cert, ⟨baireCategoryChapterTasteGate⟩⟩

end BEDC.Derived.BaireCategoryUp
