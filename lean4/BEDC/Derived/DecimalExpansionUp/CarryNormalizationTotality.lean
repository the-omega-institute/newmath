import BEDC.Derived.DecimalExpansionUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.DecimalExpansionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem DecimalExpansionCarryNormalizationTotality
    {D W Q R E normalized normalized' comparison comparison' readback readback'
      sealRead sealRead' : BHist} :
    Cont D W normalized →
      Cont D W normalized' →
        hsame normalized normalized' →
          Cont normalized Q comparison →
            Cont normalized' Q comparison' →
              Cont comparison R readback →
                Cont comparison' R readback' →
                  Cont readback E sealRead →
                    Cont readback' E sealRead' →
                      hsame comparison comparison' ∧
                        hsame readback readback' ∧ hsame sealRead sealRead' := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro _normalizedRoute _normalizedRoute' sameNormalized comparisonRoute comparisonRoute'
    readbackRoute readbackRoute' sealRoute sealRoute'
  have sameComparison : hsame comparison comparison' :=
    cont_respects_hsame sameNormalized (hsame_refl Q) comparisonRoute comparisonRoute'
  have sameReadback : hsame readback readback' :=
    cont_respects_hsame sameComparison (hsame_refl R) readbackRoute readbackRoute'
  have sameSealRead : hsame sealRead sealRead' :=
    cont_respects_hsame sameReadback (hsame_refl E) sealRoute sealRoute'
  exact ⟨sameComparison, sameReadback, sameSealRead⟩

end BEDC.Derived.DecimalExpansionUp
