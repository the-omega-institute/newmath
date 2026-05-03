import BEDC.Derived.ComplexUp

namespace BEDC.Derived.GammaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp
open BEDC.Derived.ProdUp
open BEDC.Derived.RatUp

def GammaPoleLocus (s : BHist) : Prop :=
  ∃ n : BHist, UnaryHistory n ∧ hsame s (append (BHist.e1 n) (BHist.e1 BHist.Empty))

theorem GammaPoleLocus_complex_carrier_witness {s : BHist} :
    GammaPoleLocus s ->
      ∃ n : BHist,
        UnaryHistory n ∧ hsame s (append (BHist.e1 n) (BHist.e1 BHist.Empty)) ∧
          ComplexHistoryCarrier s := by
  intro pole
  cases pole with
  | intro n data =>
      cases data with
      | intro nUnary samePole =>
          have realCarrier : RatHistoryCarrier (BHist.e1 n) := by
            exact RatHistoryCarrier_iff_positive_denominator.mpr
              (PositiveUnaryDenominator_e1_iff_unary.mpr nUnary)
          have imagCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) := by
            exact RatHistoryCarrier_iff_positive_denominator.mpr
              (PositiveUnaryDenominator_e1_iff_unary.mpr unary_empty)
          have poleCarrier :
              ComplexHistoryCarrier (append (BHist.e1 n) (BHist.e1 BHist.Empty)) := by
            exact ProdHistoryCarrier_append_intro realCarrier imagCarrier
          exact Exists.intro n
            (And.intro nUnary
              (And.intro samePole
                (ProdHistoryCarrier_hsame_transport (hsame_symm samePole) poleCarrier)))

end BEDC.Derived.GammaUp
