import BEDC.Derived.ComplexUp

namespace BEDC.Derived.ComplexUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ComplexHistoryCarrier_components_nonempty {h : BHist} :
    ComplexHistoryCarrier h ->
      ∃ real imag : BHist,
        RatUp.RatHistoryCarrier real ∧ RatUp.RatHistoryCarrier imag ∧ Cont real imag h ∧
          (hsame real BHist.Empty -> False) ∧ (hsame imag BHist.Empty -> False) := by
  intro carrier
  cases carrier with
  | intro real rest =>
      cases rest with
      | intro imag data =>
          cases data with
          | intro realCarrier rest =>
              cases rest with
              | intro imagCarrier cont =>
                  exact Exists.intro real
                    (Exists.intro imag
                      (And.intro realCarrier
                        (And.intro imagCarrier
                          (And.intro cont
                            (And.intro
                              (RatUp.RatHistoryCarrier_not_empty realCarrier)
                              (RatUp.RatHistoryCarrier_not_empty imagCarrier))))))

end BEDC.Derived.ComplexUp
