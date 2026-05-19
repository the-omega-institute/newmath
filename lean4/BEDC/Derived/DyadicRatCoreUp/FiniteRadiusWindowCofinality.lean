import BEDC.Derived.DyadicRatCoreUp.StandardSourceBridge

namespace BEDC.Derived.DyadicRatCoreUp

open BEDC.Derived.RatUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DyadicRatCoreFiniteRadiusWindowCofinality
    {mantissa exponent ledger provenance tail refinedExponent refinedLedger tail'
      refinedExponent' refinedLedger' common scale left radiusWindow terminalWindow : BHist} :
    DyadicRatCoreCarrier mantissa exponent ledger provenance →
      UnaryHistory tail →
        UnaryHistory tail' →
          Cont exponent tail refinedExponent →
            Cont refinedExponent mantissa refinedLedger →
              Cont refinedExponent tail' refinedExponent' →
                Cont refinedExponent' mantissa refinedLedger' →
                  PositiveUnaryDenominator common →
                    Cont refinedExponent' common scale →
                      Cont mantissa scale left →
                        Cont left refinedLedger' radiusWindow →
                          Cont radiusWindow provenance terminalWindow →
                            DyadicRatCoreCarrier mantissa refinedExponent' refinedLedger'
                                provenance ∧
                              PositiveUnaryDenominator refinedExponent' ∧
                                UnaryHistory radiusWindow ∧ UnaryHistory terminalWindow ∧
                                  Cont radiusWindow provenance terminalWindow := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier tailUnary tailUnary' refinedExponentRow refinedLedgerRow refinedExponentRow'
    refinedLedgerRow' commonPositive scaleRow leftRow radiusWindowRow terminalWindowRow
  have firstRefinement :=
    DyadicRatCoreCarrier_monotone_radius_obligation carrier tailUnary refinedExponentRow
      refinedLedgerRow
  have composed :=
    DyadicRatCoreCarrier_directed_refinement_common_window firstRefinement.left tailUnary'
      refinedExponentRow' refinedLedgerRow' commonPositive scaleRow leftRow radiusWindowRow
  have terminalWindowUnary : UnaryHistory terminalWindow :=
    unary_cont_closed composed.right.right.left composed.left.right.right.left terminalWindowRow
  exact
    ⟨composed.left, composed.right.left, composed.right.right.left, terminalWindowUnary,
      terminalWindowRow⟩

end BEDC.Derived.DyadicRatCoreUp
