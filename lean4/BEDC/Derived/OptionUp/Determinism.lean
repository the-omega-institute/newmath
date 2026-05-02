import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem OptionClassifierSpec_hsame_right_deterministic {h k l : BHist} :
    OptionClassifierSpec hsame (Option.some h) (Option.some k) →
      OptionClassifierSpec hsame (Option.some h) (Option.some l) → hsame k l := by
  intro left right
  exact hsame_trans (hsame_symm left) right

theorem OptionClassifierSpec_hsame_left_deterministic {h k l : BHist} :
    OptionClassifierSpec hsame (Option.some h) (Option.some k) →
      OptionClassifierSpec hsame (Option.some l) (Option.some k) → hsame h l := by
  intro left right
  exact hsame_trans left (hsame_symm right)

theorem OptionClassifierSpec_hsame_some_right_confluence {x : OptionCarrier BHist}
    {h k : BHist} :
    OptionClassifierSpec hsame x (Option.some h) →
      OptionClassifierSpec hsame x (Option.some k) → hsame h k := by
  intro left right
  cases x with
  | none =>
      cases left
  | some _ =>
      exact hsame_trans (hsame_symm left) right

end BEDC.Derived.OptionUp
