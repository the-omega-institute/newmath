import BEDC.Derived.RatUp

namespace BEDC.Derived.RatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem PositiveUnaryDenominator_append_unary_context {pref den tail : BHist} :
    UnaryHistory pref → PositiveUnaryDenominator den → UnaryHistory tail →
      PositiveUnaryDenominator
        (BEDC.FKernel.Cont.append pref (BEDC.FKernel.Cont.append den tail)) := by
  intro prefUnary positive tailUnary
  exact PositiveUnaryDenominator_append_unary_prefix prefUnary
    (PositiveUnaryDenominator_append_unary_tail positive tailUnary)

end BEDC.Derived.RatUp
