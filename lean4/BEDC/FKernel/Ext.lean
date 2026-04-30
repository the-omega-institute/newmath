import BEDC.FKernel.Mark
import BEDC.FKernel.Hist

/-! Relational extension of a history by one emitted mark. -/
namespace BEDC.FKernel.Ext

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist

inductive Ext : BHist → BMark → BHist → Prop where
  | e0 (h : BHist) : Ext h .b0 (.e0 h)
  | e1 (h : BHist) : Ext h .b1 (.e1 h)

theorem ext_deterministic :
    ∀ {h r r' : BHist} {m : BMark}, Ext h m r → Ext h m r' → hsame r r' := by
  intro h r r' m hr hr'
  cases hr <;> cases hr' <;> rfl

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

end BEDC.FKernel.Ext
