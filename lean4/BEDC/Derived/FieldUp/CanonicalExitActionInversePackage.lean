import BEDC.Derived.FieldUp.ConcreteExitObject
import BEDC.FKernel.NameCert

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.Derived.RatUp

theorem RatupFieldupCanonicalExitActionInversePackage
    {carrier denominator endpoint context support selector ledger : BHist} :
    RatupFieldupConcreteExitObject carrier denominator endpoint context support selector ledger ->
      FieldSingletonCarrier context ->
        FieldSingletonCarrier selector ->
          SemanticNameCert
              (fun row : BHist =>
                RatupFieldupConcreteExitObject carrier denominator endpoint context support
                  selector ledger ∧
                  hsame row ledger)
              (fun row : BHist =>
                hsame row ledger ∧ FieldSingletonCarrier context ∧
                  FieldSingletonCarrier selector)
              (fun row : BHist =>
                RatHistoryCarrier endpoint ∧ RatDenomUnitCarrier support ∧
                  hsame row ledger)
              hsame ∧
            RatHistoryCarrier endpoint ∧ RatDenomUnitCarrier support ∧
              Cont context carrier selector ∧ Cont selector denominator ledger ∧
                hsame endpoint carrier := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert RatHistoryCarrier
  intro exitObject contextSingleton selectorSingleton
  have exitObjectPacket :
      RatupFieldupConcreteExitObject carrier denominator endpoint context support selector ledger :=
    exitObject
  obtain ⟨_carrierRat, _denominatorUnit, carrierEndpoint, denominatorSupport,
    contextCarrier, selectorDenominator, endpointSameCarrier⟩ := exitObject
  have endpointRat : RatHistoryCarrier endpoint := carrierEndpoint.right.left
  have supportUnit : RatDenomUnitCarrier support := denominatorSupport.right.left
  have sourceLedger :
      (fun row : BHist =>
        RatupFieldupConcreteExitObject carrier denominator endpoint context support selector
          ledger ∧
          hsame row ledger) ledger := by
    exact ⟨exitObjectPacket, hsame_refl ledger⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            RatupFieldupConcreteExitObject carrier denominator endpoint context support
              selector ledger ∧
              hsame row ledger)
          (fun row : BHist =>
            hsame row ledger ∧ FieldSingletonCarrier context ∧ FieldSingletonCarrier selector)
          (fun row : BHist =>
            RatHistoryCarrier endpoint ∧ RatDenomUnitCarrier support ∧ hsame row ledger)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro ledger sourceLedger
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows source
          exact
            ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.right, contextSingleton, selectorSingleton⟩
      ledger_sound := by
        intro _row source
        exact ⟨endpointRat, supportUnit, source.right⟩
    }
  exact
    ⟨cert, endpointRat, supportUnit, contextCarrier, selectorDenominator,
      endpointSameCarrier⟩

end BEDC.Derived.FieldUp
