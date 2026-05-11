import BEDC.Derived.DyadicRatCoreUp

namespace BEDC.Derived.DyadicRatCoreUp

open BEDC.Derived.RatUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DyadicRatCoreCarrier_public_readback_envelope
    {mantissa exponent ledger provenance mantissa' exponent' ledger' provenance' common scale
      scale' left right classifierWindow tail refinedExponent refinedLedger : BHist} :
    DyadicRatCoreCarrier mantissa exponent ledger provenance ->
      DyadicRatCoreCarrier mantissa' exponent' ledger' provenance' ->
        PositiveUnaryDenominator common ->
          Cont exponent common scale ->
            Cont exponent' common scale' ->
              Cont mantissa scale left ->
                Cont mantissa' scale' right ->
                  Cont left right classifierWindow ->
                    UnaryHistory tail ->
                      Cont exponent tail refinedExponent ->
                        Cont refinedExponent mantissa refinedLedger ->
                          DyadicRatCoreCarrier mantissa refinedExponent refinedLedger
                              provenance ∧
                            UnaryHistory scale ∧
                              UnaryHistory scale' ∧
                                UnaryHistory left ∧
                                  UnaryHistory right ∧
                                    UnaryHistory classifierWindow ∧
                                      PositiveUnaryDenominator refinedExponent ∧
                                        hsame classifierWindow (append left right) ∧
                                          hsame refinedExponent (append exponent tail) ∧
                                            Cont refinedExponent mantissa refinedLedger := by
  intro carrier carrier' commonPositive scaleRow scaleRow' leftRow rightRow classifierRow
    tailUnary refinedExponentRow refinedLedgerRow
  have windowRows :=
    DyadicRatCoreCarrier_common_exponent_window_exactness carrier carrier' commonPositive
      scaleRow scaleRow' leftRow rightRow classifierRow
  have refinedRows :=
    DyadicRatCoreCarrier_monotone_radius_obligation carrier tailUnary refinedExponentRow
      refinedLedgerRow
  exact
    ⟨refinedRows.left,
      windowRows.left,
      windowRows.right.left,
      windowRows.right.right.left,
      windowRows.right.right.right.left,
      windowRows.right.right.right.right.left,
      refinedRows.right.left,
      windowRows.right.right.right.right.right.right.right,
      refinedRows.right.right.left,
      refinedRows.right.right.right⟩

end BEDC.Derived.DyadicRatCoreUp
