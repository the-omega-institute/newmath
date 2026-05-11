import BEDC.Derived.DyadicRatCoreUp

namespace BEDC.Derived.DyadicRatCoreUp

open BEDC.Derived.RatUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DyadicRatCoreCarrier_scoped_source_boundary
    {mantissa exponent ledger provenance : BHist} :
    DyadicRatCoreCarrier mantissa exponent ledger provenance ->
      RatHistoryCarrier mantissa ∧ PositiveUnaryDenominator exponent ∧
        UnaryHistory provenance ∧ Cont exponent mantissa ledger ∧ UnaryHistory ledger ∧
          hsame ledger (append exponent mantissa) := by
  intro carrier
  exact And.intro carrier.left
    (And.intro carrier.right.left
      (And.intro carrier.right.right.left
        (And.intro carrier.right.right.right.left
          (And.intro carrier.right.right.right.right carrier.right.right.right.left))))

end BEDC.Derived.DyadicRatCoreUp
