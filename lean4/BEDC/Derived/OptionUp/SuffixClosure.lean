import BEDC.Derived.OptionUp
import BEDC.FKernel.Unary

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem OptionHistoryCarrier_unary_suffix_closed {p h : BHist} :
    UnaryHistory p -> OptionHistoryCarrier UnaryHistory h ->
      OptionHistoryCarrier UnaryHistory (append h p) := by
  intro suffixCarrier carrier
  cases carrier with
  | inl emptyCase =>
      have hCarrier : UnaryHistory h := unary_transport unary_empty (hsame_symm emptyCase)
      exact Or.inr (unary_append_closed hCarrier suffixCarrier)
  | inr sourceCarrier =>
      exact Or.inr (unary_append_closed sourceCarrier suffixCarrier)

end BEDC.Derived.OptionUp
