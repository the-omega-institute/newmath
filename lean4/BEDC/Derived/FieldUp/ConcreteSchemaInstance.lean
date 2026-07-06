import BEDC.Derived.FieldUp.ConcreteExitObject

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Derived.RatUp

theorem RatupFieldupConcreteSchemaInstance
    {carrier denominator endpoint context support selector ledger : BHist} :
    RatupFieldupConcreteExitObject carrier denominator endpoint context support selector ledger →
      RatHistoryCarrier carrier ∧ RatDenomUnitCarrier denominator ∧
        Cont context carrier selector ∧ hsame endpoint carrier := by
  -- BEDC touchpoint anchor: BHist Cont hsame RatHistoryCarrier
  intro exitObject
  obtain ⟨carrierRat, denominatorUnit, _carrierEndpoint, _denominatorSupport,
    contextCarrier, _selectorDenominator, endpointSameCarrier⟩ := exitObject
  exact ⟨carrierRat, denominatorUnit, contextCarrier, endpointSameCarrier⟩

end BEDC.Derived.FieldUp
