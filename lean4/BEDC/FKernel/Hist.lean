import BEDC.FKernel.Mark

/-! Generated histories and their internal sameness relation. -/
namespace BEDC.FKernel.Hist

open BEDC.FKernel.Mark

inductive BHist where
  | Empty
  | e0 (h : BHist)
  | e1 (h : BHist)
  deriving DecidableEq, Repr

def hsame : BHist → BHist → Prop := Eq

theorem hsame_refl : ∀ h : BHist, hsame h h := by
  intro h
  rfl

theorem hsame_symm : ∀ {h k : BHist}, hsame h k → hsame k h := by
  intro h k hs
  exact hs.symm

theorem hsame_trans : ∀ {a b c : BHist}, hsame a b → hsame b c → hsame a c := by
  intro a b c hab hbc
  exact hab.trans hbc

theorem hsame_equivalence :
    (∀ h : BHist, hsame h h) ∧
      (∀ {h k : BHist}, hsame h k → hsame k h) ∧
      (∀ {a b c : BHist}, hsame a b → hsame b c → hsame a c) := by
  constructor
  · exact hsame_refl
  · constructor
    · exact hsame_symm
    · exact hsame_trans

theorem hsame_constructor_inversion :
    (∀ {h x : BHist}, hsame (.e0 h) x → ∃ k : BHist, x = .e0 k ∧ hsame h k) ∧
      (∀ {h x : BHist}, hsame (.e1 h) x → ∃ k : BHist, x = .e1 k ∧ hsame h k) := by
  constructor
  · intro h x hx
    cases hx
    exact Exists.intro h (And.intro rfl rfl)
  · intro h x hx
    cases hx
    exact Exists.intro h (And.intro rfl rfl)

theorem hsame_e1_congr {h k : BHist} : hsame h k -> hsame (.e1 h) (.e1 k) := by
  intro hs
  cases hs
  rfl

theorem hsame_e0_inversion {h x : BHist} : hsame (.e0 h) x → ∃ k : BHist, x = .e0 k ∧ hsame h k := by
  intro hs
  cases hs
  exact Exists.intro h (And.intro rfl rfl)

theorem hsame_e1_inversion {h x : BHist} : hsame (.e1 h) x → ∃ k : BHist, x = .e1 k ∧ hsame h k := by
  intro hs
  cases hs
  exact Exists.intro h (And.intro rfl rfl)

theorem not_hsame_emp_e0 : ∀ {h : BHist}, hsame .Empty (.e0 h) → False := by
  intro h hs
  cases hs

theorem not_hsame_emp_e1 : ∀ {h : BHist}, hsame .Empty (.e1 h) → False := by
  intro h hs
  cases hs

theorem not_hsame_e0_e1 : ∀ {h k : BHist}, hsame (.e0 h) (.e1 k) → False := by
  intro h k hs
  cases hs

theorem not_hsame_e1_e0 : forall {h k : BHist}, hsame (.e1 h) (.e0 k) -> False := by
  intro h k hs
  cases hs

end BEDC.FKernel.Hist
