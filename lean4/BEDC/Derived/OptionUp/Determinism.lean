import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem OptionClassifierSpec_hsame_right_deterministic {h k l : BHist} :
    OptionClassifierSpec hsame (Option.some h) (Option.some k) →
      OptionClassifierSpec hsame (Option.some h) (Option.some l) → hsame k l := by
  intro left right
  exact hsame_trans (hsame_symm left) right

end BEDC.Derived.OptionUp
