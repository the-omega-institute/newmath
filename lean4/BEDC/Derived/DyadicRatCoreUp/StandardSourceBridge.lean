import BEDC.Derived.DyadicRatCoreUp

namespace BEDC.Derived.DyadicRatCoreUp

open BEDC.Derived.RatUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DyadicRatCoreCarrier_standard_source_bridge
    {mantissa exponent ledger provenance mantissa' exponent' ledger' provenance' common scale
      scale' classifierWindow : BHist} :
    DyadicRatCoreCarrier mantissa exponent ledger provenance ->
      DyadicRatCoreCarrier mantissa' exponent' ledger' provenance' ->
        PositiveUnaryDenominator common ->
          hsame provenance provenance' ->
            Cont exponent common scale ->
              Cont exponent' common scale' ->
                RatHistoryClassifier scale scale' ->
                  Cont scale scale' classifierWindow ->
                    DyadicRatCoreClassifier mantissa exponent ledger provenance mantissa'
                        exponent' ledger' provenance' common scale scale' ∧
                      UnaryHistory scale ∧ UnaryHistory scale' ∧ UnaryHistory classifierWindow ∧
                        hsame classifierWindow (append scale scale') := by
  intro carrier carrier' commonPositive sameProvenance scaleRow scaleRow' classified
    classifierRow
  have exponentUnary : UnaryHistory exponent :=
    (PositiveUnaryDenominator_unary_and_nonempty carrier.right.left).left
  have exponentUnary' : UnaryHistory exponent' :=
    (PositiveUnaryDenominator_unary_and_nonempty carrier'.right.left).left
  have commonUnary : UnaryHistory common :=
    (PositiveUnaryDenominator_unary_and_nonempty commonPositive).left
  have scaleUnary : UnaryHistory scale :=
    unary_cont_closed exponentUnary commonUnary scaleRow
  have scaleUnary' : UnaryHistory scale' :=
    unary_cont_closed exponentUnary' commonUnary scaleRow'
  have classifierWindowUnary : UnaryHistory classifierWindow :=
    unary_cont_closed scaleUnary scaleUnary' classifierRow
  have classifiedCore :
      DyadicRatCoreClassifier mantissa exponent ledger provenance mantissa' exponent' ledger'
        provenance' common scale scale' :=
    And.intro carrier
      (And.intro carrier'
        (And.intro commonPositive
          (And.intro scaleRow
            (And.intro scaleRow' (And.intro classified sameProvenance)))))
  exact And.intro classifiedCore
    (And.intro scaleUnary
      (And.intro scaleUnary' (And.intro classifierWindowUnary classifierRow)))

theorem DyadicRatCoreCarrier_standard_bridge_denominator_refinement_stability
    {mantissa exponent ledger provenance tail refinedExponent refinedLedger common scale left
      distanceWindow : BHist} :
    DyadicRatCoreCarrier mantissa exponent ledger provenance ->
      UnaryHistory tail ->
        Cont exponent tail refinedExponent ->
          Cont refinedExponent mantissa refinedLedger ->
            PositiveUnaryDenominator common ->
              Cont exponent common scale ->
                Cont mantissa scale left ->
                  Cont left refinedLedger distanceWindow ->
                    DyadicRatCoreCarrier mantissa refinedExponent refinedLedger provenance ∧
                      PositiveUnaryDenominator refinedExponent ∧
                        UnaryHistory distanceWindow ∧
                          hsame refinedExponent (append exponent tail) ∧
                            Cont left refinedLedger distanceWindow := by
  intro carrier tailUnary refinedExponentRow refinedLedgerRow commonPositive scaleRow leftRow
    distanceWindowRow
  have refinedRows :=
    DyadicRatCoreCarrier_monotone_radius_obligation carrier tailUnary refinedExponentRow
      refinedLedgerRow
  have exponentUnary : UnaryHistory exponent :=
    (PositiveUnaryDenominator_unary_and_nonempty carrier.right.left).left
  have commonUnary : UnaryHistory common :=
    (PositiveUnaryDenominator_unary_and_nonempty commonPositive).left
  have scaleUnary : UnaryHistory scale :=
    unary_cont_closed exponentUnary commonUnary scaleRow
  have mantissaUnary : UnaryHistory mantissa :=
    (PositiveUnaryDenominator_unary_and_nonempty
      (RatHistoryCarrier_iff_positive_denominator.mp carrier.left)).left
  have leftUnary : UnaryHistory left :=
    unary_cont_closed mantissaUnary scaleUnary leftRow
  have refinedLedgerUnary : UnaryHistory refinedLedger :=
    refinedRows.left.right.right.right.right
  have distanceWindowUnary : UnaryHistory distanceWindow :=
    unary_cont_closed leftUnary refinedLedgerUnary distanceWindowRow
  exact And.intro refinedRows.left
    (And.intro refinedRows.right.left
      (And.intro distanceWindowUnary
        (And.intro refinedRows.right.right.left distanceWindowRow)))

end BEDC.Derived.DyadicRatCoreUp
