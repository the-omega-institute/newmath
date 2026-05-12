import BEDC.Derived.FieldUp.RatDenomUnit

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

def FieldCertificateObligations
    (source carrier classifier ringBase inverseData productData denominatorTuple contextualData
      affineSource ledgerExactness status : BHist) : Prop :=
  RatHistoryCarrier carrier ∧ RatHistoryClassifier carrier classifier ∧
    RatDenomUnitCarrier denominatorTuple ∧
      RatDenomUnitClassifier denominatorTuple contextualData ∧
        hsame source (append carrier classifier) ∧
          hsame ringBase (append productData inverseData) ∧
            hsame affineSource (append contextualData ledgerExactness) ∧
              hsame status (append source affineSource)

theorem FieldCertificateObligations_rat_denominator_rows
    {source carrier classifier ringBase inverseData productData denominatorTuple contextualData
      affineSource ledgerExactness status : BHist} :
    FieldCertificateObligations source carrier classifier ringBase inverseData productData
        denominatorTuple contextualData affineSource ledgerExactness status ->
      RatHistoryCarrier carrier ∧ RatHistoryClassifier carrier classifier ∧
        RatDenomUnitCarrier denominatorTuple ∧
          RatDenomUnitClassifier denominatorTuple contextualData ∧
            hsame source (append carrier classifier) ∧
              hsame ringBase (append productData inverseData) ∧
                hsame affineSource (append contextualData ledgerExactness) ∧
                  hsame status (append source affineSource) := by
  intro obligations
  exact obligations

end BEDC.Derived.FieldUp
