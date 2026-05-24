import BEDC.Derived.FieldUp.RatDenomUnit

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem RatupFieldupAssembledCertificateBoundary :
    SemanticNameCert FieldSingletonCarrier FieldSingletonCarrier FieldSingletonCarrier
        FieldSingletonClassifier ∧
      RatDenomUnitCarrier BHist.Empty ∧
      FieldSingletonCarrier BHist.Empty ∧
      FieldSingletonClassifier (FieldSingletonMul FieldSingletonOne FieldSingletonOne)
        FieldSingletonOne ∧
      hsame (append BHist.Empty BHist.Empty) BHist.Empty := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  have singletonCert :
      SemanticNameCert FieldSingletonCarrier FieldSingletonCarrier FieldSingletonCarrier
        FieldSingletonClassifier :=
    singleton_empty_history_field_schema_laws.left
  have denomCarrier : RatDenomUnitCarrier BHist.Empty :=
    Or.inl (hsame_refl BHist.Empty)
  have emptyCarrier : FieldSingletonCarrier BHist.Empty :=
    hsame_refl BHist.Empty
  have mulOneCarrier :
      FieldSingletonCarrier (FieldSingletonMul FieldSingletonOne FieldSingletonOne) := by
    unfold FieldSingletonMul FieldSingletonCarrier
    exact hsame_refl BHist.Empty
  have oneCarrier : FieldSingletonCarrier FieldSingletonOne := by
    unfold FieldSingletonOne FieldSingletonCarrier
    exact hsame_refl BHist.Empty
  have mulOneClassifier :
      FieldSingletonClassifier (FieldSingletonMul FieldSingletonOne FieldSingletonOne)
        FieldSingletonOne :=
    ⟨mulOneCarrier, oneCarrier, hsame_refl BHist.Empty⟩
  exact
    ⟨singletonCert, denomCarrier, emptyCarrier, mulOneClassifier,
      hsame_refl BHist.Empty⟩

end BEDC.Derived.FieldUp
