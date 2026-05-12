import BEDC.Derived.FpsUp

namespace BEDC.Derived.FpsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

theorem FpsUp_StdBridge {F G n endpoint : BHist} :
    FpsSingletonCarrier F ->
      FpsSingletonCarrier G ->
        Cont (FpsSingletonCoeff F n) (FpsSingletonCoeff G n) endpoint ->
          FpsSingletonCarrier endpoint ∧
            FpsSingletonClassifier endpoint FpsSingletonZero ∧
              SemanticNameCert FpsSingletonCarrier FpsSingletonCarrier FpsSingletonCarrier
                FpsSingletonClassifier := by
  intro _carrierF _carrierG coeffRoute
  have endpointCarrier : FpsSingletonCarrier endpoint :=
    hsame_trans coeffRoute
      (append_eq_empty_iff.mpr
        (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)))
  have zeroCarrier : FpsSingletonCarrier FpsSingletonZero :=
    hsame_refl BHist.Empty
  have endpointClassifier : FpsSingletonClassifier endpoint FpsSingletonZero :=
    And.intro endpointCarrier
      (And.intro zeroCarrier (hsame_trans endpointCarrier (hsame_symm zeroCarrier)))
  exact ⟨endpointCarrier, endpointClassifier, (fps_singleton_empty_schema_laws).left⟩

end BEDC.Derived.FpsUp
