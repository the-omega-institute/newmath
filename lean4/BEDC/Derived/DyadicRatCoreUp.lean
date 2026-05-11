import BEDC.Derived.RatUp

namespace BEDC.Derived.DyadicRatCoreUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem DyadicRatCore_denominator_ledger_transport_window
    {den den' tail route route' : BHist} :
    PositiveUnaryDenominator den -> UnaryHistory tail -> hsame den den' ->
      Cont den tail route -> Cont den' tail route' ->
        PositiveUnaryDenominator den' ∧ PositiveUnaryDenominator (append den' tail) ∧
          hsame route (append den tail) ∧ hsame route' (append den' tail) := by
  intro denPositive tailUnary sameDen routeCont routeCont'
  have denPositive' : PositiveUnaryDenominator den' :=
    PositiveUnaryDenominator_hsame_transport sameDen denPositive
  exact And.intro denPositive'
    (And.intro (PositiveUnaryDenominator_append_unary_tail denPositive' tailUnary)
      (And.intro routeCont routeCont'))

def DyadicRatCoreCarrier (mantissa exponent ledger provenance : BHist) : Prop :=
  RatHistoryCarrier mantissa ∧ PositiveUnaryDenominator exponent ∧ UnaryHistory provenance ∧
    Cont exponent mantissa ledger ∧ UnaryHistory ledger

theorem DyadicRatCoreCarrier_denominator_transport
    {mantissa exponent ledger provenance mantissa' exponent' ledger' provenance' : BHist} :
    DyadicRatCoreCarrier mantissa exponent ledger provenance ->
      hsame mantissa mantissa' -> hsame exponent exponent' -> hsame provenance provenance' ->
        Cont exponent' mantissa' ledger' ->
          DyadicRatCoreCarrier mantissa' exponent' ledger' provenance' ∧ hsame ledger ledger' ∧
            RatHistoryCarrier mantissa' ∧ PositiveUnaryDenominator exponent' ∧
              UnaryHistory ledger' := by
  intro carrier sameMantissa sameExponent sameProvenance contLedger'
  have mantissaCarrier : RatHistoryCarrier mantissa := carrier.left
  have exponentPositive : PositiveUnaryDenominator exponent := carrier.right.left
  have provenanceUnary : UnaryHistory provenance := carrier.right.right.left
  have contLedger : Cont exponent mantissa ledger := carrier.right.right.right.left
  have mantissaCarrier' : RatHistoryCarrier mantissa' :=
    RatHistoryCarrier_hsame_transport sameMantissa mantissaCarrier
  have exponentPositive' : PositiveUnaryDenominator exponent' :=
    PositiveUnaryDenominator_hsame_transport sameExponent exponentPositive
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have exponentUnary' : UnaryHistory exponent' :=
    (PositiveUnaryDenominator_unary_and_nonempty exponentPositive').left
  have ledgerSame : hsame ledger ledger' :=
    cont_respects_hsame sameExponent sameMantissa contLedger contLedger'
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed exponentUnary' (RatHistoryCarrier_iff_positive_denominator.mp
      mantissaCarrier' |> PositiveUnaryDenominator_unary_and_nonempty |>.left) contLedger'
  have carrier' : DyadicRatCoreCarrier mantissa' exponent' ledger' provenance' :=
    And.intro mantissaCarrier'
      (And.intro exponentPositive'
        (And.intro provenanceUnary' (And.intro contLedger' ledgerUnary')))
  exact And.intro carrier'
    (And.intro ledgerSame
      (And.intro mantissaCarrier' (And.intro exponentPositive' ledgerUnary')))

end BEDC.Derived.DyadicRatCoreUp
