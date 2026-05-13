import BEDC.Derived.FieldUp.RatDenomUnit

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

def RatupFieldupConcreteExitObject
    (carrier denominator endpoint context support selector ledger : BHist) : Prop :=
  RatHistoryCarrier carrier ∧ RatDenomUnitCarrier denominator ∧
    RatHistoryClassifier carrier endpoint ∧ RatDenomUnitClassifier denominator support ∧
      Cont context carrier selector ∧ Cont selector denominator ledger ∧
        hsame endpoint carrier

theorem RatupFieldupConcreteExitObjectComplete
    {carrier denominator endpoint context support selector ledger : BHist} :
    RatHistoryCarrier carrier -> RatDenomUnitCarrier denominator ->
      RatHistoryClassifier carrier endpoint -> RatDenomUnitClassifier denominator support ->
        Cont context carrier selector -> Cont selector denominator ledger ->
          RatupFieldupConcreteExitObject carrier denominator endpoint context support selector
              ledger ∧
            RatHistoryCarrier endpoint ∧ RatDenomUnitCarrier support ∧ hsame endpoint carrier := by
  intro carrierRat denominatorUnit carrierEndpoint denominatorSupport contextCarrier
    selectorDenominator
  have endpointRat : RatHistoryCarrier endpoint := carrierEndpoint.right.left
  have endpointSameCarrier : hsame endpoint carrier := hsame_symm carrierEndpoint.right.right
  have supportUnit : RatDenomUnitCarrier support := denominatorSupport.right.left
  exact
    ⟨⟨carrierRat, denominatorUnit, carrierEndpoint, denominatorSupport, contextCarrier,
      selectorDenominator, endpointSameCarrier⟩, endpointRat, supportUnit,
        endpointSameCarrier⟩

end BEDC.Derived.FieldUp
