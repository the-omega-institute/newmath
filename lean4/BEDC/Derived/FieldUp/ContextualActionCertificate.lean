import BEDC.Derived.FieldUp.ContextualAction

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem RatupFieldupDenominatorContextualAction_certificate {h k l r p q p' q' : BHist} :
    RatDenomUnitCarrier h ->
      RatDenomUnitCarrier k ->
        RatDenomUnitCarrier l ->
          RatDenomUnitCarrier r ->
            hsame p BHist.Empty ->
              hsame q BHist.Empty ->
                hsame p' BHist.Empty ->
                  hsame q' BHist.Empty ->
                    (RatDenomUnitClassifier (RatDenomUnitContextualAction p q l r h)
                        (RatDenomUnitContextualAction p' q' l r k) ↔
                      RatDenomUnitClassifier h k) := by
  intro carrierH carrierK carrierL carrierR sameP sameQ sameP' sameQ'
  have coreIff :
      RatDenomUnitClassifier (append (append l h) r) (append (append l k) r) ↔
        RatDenomUnitClassifier h k :=
    field_rat_denominator_empty_unit_bilateral_multiplication_classifier_exactness carrierH
      carrierK carrierL carrierR
  have contextIff :
      RatDenomUnitClassifier
          (append p (append (append (append l h) r) q))
          (append p' (append (append (append l k) r) q')) ↔
        RatDenomUnitClassifier (append (append l h) r) (append (append l k) r) :=
    RatDenomUnitClassifier_empty_context_iff (p := p) (q := q) (p' := p') (q' := q')
      (h := append (append l h) r) (k := append (append l k) r) sameP sameQ sameP'
      sameQ'
  constructor
  · intro classified
    exact Iff.mp coreIff (Iff.mp contextIff classified)
  · intro classified
    exact Iff.mpr contextIff (Iff.mpr coreIff classified)

end BEDC.Derived.FieldUp
