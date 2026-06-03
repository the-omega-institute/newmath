import BEDC.Derived.FieldUp.ConcreteExitObject

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RatupFieldupAffineCentralizerNormalizerAction
    {carrier denominator endpoint context support selector ledger center normalizer actionRead :
      BHist} :
    RatupFieldupConcreteExitObject carrier denominator endpoint context support selector ledger →
      Cont endpoint carrier center →
        Cont center denominator normalizer →
          Cont normalizer center actionRead →
            RatHistoryCarrier carrier ∧ RatDenomUnitCarrier denominator ∧
              RatHistoryClassifier carrier endpoint ∧ UnaryHistory center ∧
                UnaryHistory normalizer ∧ UnaryHistory actionRead ∧ hsame endpoint carrier ∧
                  Cont normalizer center actionRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame RatHistoryCarrier RatDenomUnitCarrier
  intro exitObject centerRoute normalizerRoute actionRoute
  obtain
    ⟨carrierRat, denominatorUnit, carrierEndpoint, _denominatorSupport, _contextCarrier,
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
  have actionUnary : UnaryHistory actionRead :=
    unary_cont_closed normalizerUnary centerUnary actionRoute
  exact
    ⟨carrierRat, denominatorUnit, carrierEndpoint, centerUnary, normalizerUnary,
      actionUnary, sameEndpointCarrier, actionRoute⟩

end BEDC.Derived.FieldUp
