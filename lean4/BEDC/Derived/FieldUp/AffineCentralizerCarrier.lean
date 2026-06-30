import BEDC.Derived.FieldUp.AffineCentralizerNormalizerAction
import BEDC.Derived.FieldUp.AffineCentralizerNormalizerSubgroup

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

def RatupFieldupAffineCentralizerCarrier
    (carrier denominator endpoint context support selector ledger center : BHist) : Prop :=
  RatupFieldupConcreteExitObject carrier denominator endpoint context support selector ledger ∧
    Cont endpoint carrier center

theorem RatupFieldupAffineCentralizerSubgroup
    {carrier denominator endpoint context support selector ledger center normalizer actionRead
      readback : BHist} :
    RatupFieldupConcreteExitObject carrier denominator endpoint context support selector ledger ->
      Cont endpoint carrier center ->
        Cont center denominator normalizer ->
          Cont normalizer center actionRead ->
            Cont normalizer support readback ->
              RatupFieldupAffineCentralizerCarrier carrier denominator endpoint context support
                  selector ledger center ∧
                UnaryHistory center ∧ UnaryHistory normalizer ∧ UnaryHistory actionRead ∧
                  UnaryHistory readback ∧ RatHistoryCarrier carrier ∧
                    RatDenomUnitCarrier denominator ∧ RatHistoryClassifier carrier endpoint ∧
                      RatDenomUnitClassifier denominator support ∧ hsame endpoint carrier := by
  -- BEDC touchpoint anchor: BHist Cont hsame RatHistoryCarrier RatDenomUnitCarrier
  intro exitObject centerRoute normalizerRoute actionRoute readbackRoute
  have subgroup :=
    RatupFieldupAffineCentralizerNormalizerSubgroup
      exitObject
      centerRoute
      normalizerRoute
      readbackRoute
  have action :=
    RatupFieldupAffineCentralizerNormalizerAction
      exitObject
      centerRoute
      normalizerRoute
      actionRoute
  obtain
    ⟨centerUnary, normalizerUnary, readbackUnary, carrierRat, denominatorUnit,
      carrierEndpoint, denominatorSupport, sameEndpointCarrier, _centerRoute,
      _normalizerRoute, _readbackRoute⟩ := subgroup
  obtain
    ⟨_actionCarrierRat, _actionDenominatorUnit, _actionCarrierEndpoint,
      _actionCenterUnary, _actionNormalizerUnary, actionUnary, _actionSameEndpointCarrier,
      _actionRoute⟩ := action
  exact
    ⟨⟨exitObject, centerRoute⟩, centerUnary, normalizerUnary, actionUnary, readbackUnary,
      carrierRat, denominatorUnit, carrierEndpoint, denominatorSupport, sameEndpointCarrier⟩

end BEDC.Derived.FieldUp
