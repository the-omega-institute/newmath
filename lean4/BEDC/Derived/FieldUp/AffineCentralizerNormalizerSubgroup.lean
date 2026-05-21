import BEDC.Derived.FieldUp.ConcreteExitObject

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RatupFieldupAffineCentralizerNormalizerSubgroup
    {carrier denominator endpoint context support selector ledger center normalizer readback :
      BHist} :
    RatupFieldupConcreteExitObject carrier denominator endpoint context support selector ledger ->
      Cont endpoint carrier center ->
        Cont center denominator normalizer ->
          Cont normalizer support readback ->
            UnaryHistory center ∧ UnaryHistory normalizer ∧ UnaryHistory readback ∧
              RatHistoryCarrier carrier ∧ RatDenomUnitCarrier denominator ∧
                RatHistoryClassifier carrier endpoint ∧
                  RatDenomUnitClassifier denominator support ∧ hsame endpoint carrier ∧
                    Cont endpoint carrier center ∧ Cont center denominator normalizer ∧
                      Cont normalizer support readback := by
  -- BEDC touchpoint anchor: BHist Cont hsame RatHistoryCarrier RatDenomUnitCarrier
  intro exitObject centerRoute normalizerRoute readbackRoute
  obtain
    ⟨carrierRat, denominatorUnit, carrierEndpoint, denominatorSupport, _contextCarrier,
      _selectorDenominator, sameEndpointCarrier⟩ := exitObject
  have endpointRat : RatHistoryCarrier endpoint :=
    carrierEndpoint.right.left
  have carrierUnary : UnaryHistory carrier :=
    (PositiveUnaryDenominator_unary_and_nonempty
      (RatHistoryCarrier_iff_positive_denominator.mp carrierRat)).left
  have endpointUnary : UnaryHistory endpoint :=
    (PositiveUnaryDenominator_unary_and_nonempty
      (RatHistoryCarrier_iff_positive_denominator.mp endpointRat)).left
  have centerUnary : UnaryHistory center :=
    unary_cont_closed endpointUnary carrierUnary centerRoute
  have denominatorUnary : UnaryHistory denominator := by
    cases denominatorUnit with
    | inl emptyDenominator =>
        exact unary_transport unary_empty (hsame_symm emptyDenominator)
    | inr denominatorRat =>
        exact
          (PositiveUnaryDenominator_unary_and_nonempty
            (RatHistoryCarrier_iff_positive_denominator.mp denominatorRat)).left
  have normalizerUnary : UnaryHistory normalizer :=
    unary_cont_closed centerUnary denominatorUnary normalizerRoute
  have supportUnit : RatDenomUnitCarrier support :=
    denominatorSupport.right.left
  have supportUnary : UnaryHistory support := by
    cases supportUnit with
    | inl emptySupport =>
        exact unary_transport unary_empty (hsame_symm emptySupport)
    | inr supportRat =>
        exact
          (PositiveUnaryDenominator_unary_and_nonempty
            (RatHistoryCarrier_iff_positive_denominator.mp supportRat)).left
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed normalizerUnary supportUnary readbackRoute
  exact
    ⟨centerUnary, normalizerUnary, readbackUnary, carrierRat, denominatorUnit, carrierEndpoint,
      denominatorSupport, sameEndpointCarrier, centerRoute, normalizerRoute, readbackRoute⟩

end BEDC.Derived.FieldUp
