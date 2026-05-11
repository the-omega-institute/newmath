import BEDC.Derived.DyadicRatCoreUp
import BEDC.Derived.RealUp.Core

namespace BEDC.Derived.DyadicRatCoreUp

open BEDC.Derived.RatUp
open BEDC.Derived.RealUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DyadicRatCoreCarrier_real_phase_source_coverage
    {mantissa exponent ledger provenance mantissa' realRow window window' : BHist} :
    DyadicRatCoreCarrier mantissa exponent ledger provenance ->
      hsame mantissa mantissa' ->
        Cont (BHist.e1 mantissa') exponent realRow ->
          Cont realRow ledger window ->
            hsame window window' ->
              RealConstantHistoryCarrier (BHist.e1 mantissa') ∧
                PositiveUnaryDenominator exponent ∧
                  UnaryHistory ledger ∧
                    UnaryHistory window' ∧
                      hsame realRow (append (BHist.e1 mantissa') exponent) ∧
                        hsame window' (append realRow ledger) := by
  intro carrier sameMantissa realRowCont windowCont sameWindow
  have mantissaCarrier' : RatHistoryCarrier mantissa' :=
    RatHistoryCarrier_hsame_transport sameMantissa carrier.left
  have realCarrier : RealConstantHistoryCarrier (BHist.e1 mantissa') :=
    RealConstantHistoryCarrier_e1_iff_rat.mpr mantissaCarrier'
  have exponentPositive : PositiveUnaryDenominator exponent := carrier.right.left
  have exponentUnary : UnaryHistory exponent :=
    (PositiveUnaryDenominator_unary_and_nonempty exponentPositive).left
  have ledgerUnary : UnaryHistory ledger := carrier.right.right.right.right
  have mantissaUnary' : UnaryHistory mantissa' :=
    (PositiveUnaryDenominator_unary_and_nonempty
      (RatHistoryCarrier_iff_positive_denominator.mp mantissaCarrier')).left
  have realHeadUnary : UnaryHistory (BHist.e1 mantissa') :=
    unary_e1_closed mantissaUnary'
  have realRowUnary : UnaryHistory realRow :=
    unary_cont_closed realHeadUnary exponentUnary realRowCont
  have windowUnary : UnaryHistory window :=
    unary_cont_closed realRowUnary ledgerUnary windowCont
  have windowUnary' : UnaryHistory window' :=
    unary_transport windowUnary sameWindow
  have sameWindowAppend : hsame window' (append realRow ledger) :=
    hsame_trans (hsame_symm sameWindow) windowCont
  exact And.intro realCarrier
    (And.intro exponentPositive
      (And.intro ledgerUnary
        (And.intro windowUnary'
          (And.intro realRowCont sameWindowAppend))))

theorem DyadicRatCoreCarrier_public_bridge_consumer_exactness
    {mantissa exponent ledger provenance tail refinedExponent refinedLedger mantissa' realRow
      window window' : BHist} :
    DyadicRatCoreCarrier mantissa exponent ledger provenance ->
      UnaryHistory tail ->
        Cont exponent tail refinedExponent ->
          Cont refinedExponent mantissa refinedLedger ->
            hsame mantissa mantissa' ->
              Cont (BHist.e1 mantissa') exponent realRow ->
                Cont realRow ledger window ->
                  hsame window window' ->
                    DyadicRatCoreCarrier mantissa refinedExponent refinedLedger provenance ∧
                      RealConstantHistoryCarrier (BHist.e1 mantissa') ∧
                        PositiveUnaryDenominator refinedExponent ∧
                          UnaryHistory window' ∧ hsame window' (append realRow ledger) := by
  intro carrier tailUnary refinedExponentRow refinedLedgerRow sameMantissa realRowCont windowCont
    sameWindow
  have refinementRows :=
    DyadicRatCoreCarrier_monotone_radius_obligation carrier tailUnary refinedExponentRow
      refinedLedgerRow
  have sourceRows :=
    DyadicRatCoreCarrier_real_phase_source_coverage carrier sameMantissa realRowCont windowCont
      sameWindow
  exact And.intro refinementRows.left
    (And.intro sourceRows.left
      (And.intro refinementRows.right.left
        (And.intro sourceRows.right.right.right.left
          sourceRows.right.right.right.right.right)))

end BEDC.Derived.DyadicRatCoreUp
