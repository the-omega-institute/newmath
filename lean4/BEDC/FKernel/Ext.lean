import BEDC.FKernel.Mark
import BEDC.FKernel.Hist

/-! Relational extension of a history by one emitted mark. -/
namespace BEDC.FKernel.Ext

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist

inductive Ext : BHist → BMark → BHist → Prop where
  | e0 (h : BHist) : Ext h .b0 (.e0 h)
  | e1 (h : BHist) : Ext h .b1 (.e1 h)

theorem ext_generation_rules (h : BHist) :
    Ext h BMark.b0 (BHist.e0 h) /\ Ext h BMark.b1 (BHist.e1 h) := by
  constructor
  · exact Ext.e0 h
  · exact Ext.e1 h

theorem ext_total : ∀ (h : BHist) (m : BMark), ∃ r : BHist, Ext h m r := by
  intro h m
  cases m
  · exact Exists.intro (BHist.e0 h) (Ext.e0 h)
  · exact Exists.intro (BHist.e1 h) (Ext.e1 h)

theorem ext_deterministic :
    ∀ {h r r' : BHist} {m : BMark}, Ext h m r → Ext h m r' → hsame r r' := by
  intro h r r' m hr hr'
  cases hr <;> cases hr' <;> rfl

theorem ext_mark_deterministic_from_result :
    ∀ {h r : BHist} {m n : BMark}, Ext h m r → Ext h n r → msame m n := by
  intro h r m n hr hs
  cases hr <;> cases hs <;> rfl

theorem ext_respects_sameness :
    ∀ {h h' r r' : BHist} {m m' : BMark},
      hsame h h' → msame m m' → Ext h m r → Ext h' m' r' → hsame r r' := by
  intro h h' r r' m m' hh hm hr hr'
  cases hh
  cases hm
  cases hr <;> cases hr' <;> rfl

theorem ext_constructor_inversion {h r : BHist} {m : BMark} :
    Ext h m r ->
      (m = BMark.b0 /\ r = BHist.e0 h) \/ (m = BMark.b1 /\ r = BHist.e1 h) := by
  intro hr
  cases hr
  ·
      exact Or.inl (And.intro rfl rfl)
  ·
      exact Or.inr (And.intro rfl rfl)

theorem ext_constructor_characterization {h r : BHist} {m : BMark} :
    Ext h m r ↔ (m = BMark.b0 ∧ r = BHist.e0 h) ∨ (m = BMark.b1 ∧ r = BHist.e1 h) := by
  constructor
  ·
      intro hr
      cases hr
      ·
          exact Or.inl (And.intro rfl rfl)
      ·
          exact Or.inr (And.intro rfl rfl)
  ·
      intro hcase
      cases hcase with
      | inl left =>
          cases left with
          | intro hm hr =>
              cases hm
              cases hr
              exact Ext.e0 h
      | inr right =>
          cases right with
          | intro hm hr =>
              cases hm
              cases hr
              exact Ext.e1 h

end BEDC.FKernel.Ext
