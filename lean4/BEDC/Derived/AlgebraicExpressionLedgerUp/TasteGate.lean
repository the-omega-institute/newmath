import BEDC.Derived.AlgebraicExpressionLedgerUp
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AlgebraicExpressionLedgerUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

instance algebraicExpressionLedgerBHistCarrier :
    BHistCarrier _root_.BEDC.Derived.AlgebraicExpressionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow :=
    _root_.BEDC.Derived.AlgebraicExpressionLedgerUp.algebraicExpressionLedgerToEventFlow
  fromEventFlow :=
    _root_.BEDC.Derived.AlgebraicExpressionLedgerUp.algebraicExpressionLedgerFromEventFlow

instance algebraicExpressionLedgerChapterTasteGate :
    ChapterTasteGate _root_.BEDC.Derived.AlgebraicExpressionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    exact AlgebraicExpressionLedgerTasteGate_single_carrier_alignment.right.left x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (AlgebraicExpressionLedgerTasteGate_single_carrier_alignment.right.right.left x y heq)

instance algebraicExpressionLedgerFieldFaithful :
    FieldFaithful _root_.BEDC.Derived.AlgebraicExpressionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | _root_.BEDC.Derived.AlgebraicExpressionLedgerUp.mk e o a u s h c p n =>
        [e, o, a, u, s, h, c, p, n]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk e₁ o₁ a₁ u₁ s₁ h₁ c₁ p₁ n₁ =>
        cases y with
        | mk e₂ o₂ a₂ u₂ s₂ h₂ c₂ p₂ n₂ =>
            cases hfields
            rfl

instance algebraicExpressionLedgerNontrivial :
    Nontrivial _root_.BEDC.Derived.AlgebraicExpressionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨_root_.BEDC.Derived.AlgebraicExpressionLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      _root_.BEDC.Derived.AlgebraicExpressionLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem AlgebraicExpressionLedgerCarrier_nonescape :
    Nonempty (BHistCarrier _root_.BEDC.Derived.AlgebraicExpressionLedgerUp) ∧
      Nonempty (ChapterTasteGate _root_.BEDC.Derived.AlgebraicExpressionLedgerUp) ∧
        Nonempty (FieldFaithful _root_.BEDC.Derived.AlgebraicExpressionLedgerUp) ∧
          Nonempty (Nontrivial _root_.BEDC.Derived.AlgebraicExpressionLedgerUp) ∧
            _root_.BEDC.Derived.AlgebraicExpressionLedgerUp.algebraicExpressionLedgerEncodeBHist
                BHist.Empty =
              ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨algebraicExpressionLedgerBHistCarrier⟩,
      ⟨algebraicExpressionLedgerChapterTasteGate⟩,
      ⟨algebraicExpressionLedgerFieldFaithful⟩,
      ⟨algebraicExpressionLedgerNontrivial⟩,
      rfl⟩

end BEDC.Derived.AlgebraicExpressionLedgerUp.TasteGate
