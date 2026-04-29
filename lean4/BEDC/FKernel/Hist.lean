import BEDC.FKernel.Mark

/-! Generated histories and their internal sameness relation. -/
namespace BEDC.FKernel.Hist

open BEDC.FKernel.Mark


axiom BHist : Type
axiom Empty : BHist
axiom e0 : BHist → BHist
axiom e1 : BHist → BHist
axiom hsame : BHist → BHist → Prop

theorem hsame_refl : ∀ h : BHist, hsame h h := by
  sorry

theorem hsame_symm : ∀ {h k : BHist}, hsame h k → hsame k h := by
  sorry

theorem hsame_trans : ∀ {a b c : BHist}, hsame a b → hsame b c → hsame a c := by
  sorry

theorem not_hsame_emp_e0 : ∀ {h : BHist}, hsame Empty (e0 h) → False := by
  sorry

theorem not_hsame_emp_e1 : ∀ {h : BHist}, hsame Empty (e1 h) → False := by
  sorry

theorem not_hsame_e0_e1 : ∀ {h k : BHist}, hsame (e0 h) (e1 k) → False := by
  sorry

end BEDC.FKernel.Hist
