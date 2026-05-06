import BEDC.Derived.FpsUp

namespace BEDC.Derived.FpsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

theorem fps_stability_certificate_fields :
    SemanticNameCert FpsSingletonEmptyHistoryCarrier FpsSingletonEmptyHistoryCarrier
      FpsSingletonEmptyHistoryCarrier FpsSingletonEmptyHistoryClassifier ∧
    (forall {F G left right : BHist}, FpsSingletonEmptyHistoryCarrier F ->
      FpsSingletonEmptyHistoryCarrier G -> Cont F G left -> Cont G F right ->
        FpsSingletonEmptyHistoryCarrier left ∧ FpsSingletonEmptyHistoryCarrier right ∧
          FpsSingletonEmptyHistoryClassifier left right) ∧
    (forall {xs ys : List BHist},
      BEDC.Derived.ListUp.ListClassifierSpec hsame xs ys ->
        FpsSingletonAddFoldSpineCarrier xs ->
          FpsSingletonAddFoldSpineCarrier ys ∧
            hsame (append (FpsSingletonAddFold xs) BHist.Empty)
              (append (FpsSingletonAddFold ys) BHist.Empty)) := by
  constructor
  · exact FpsSingletonEmptyHistory_semanticNameCert
  · constructor
    · intro F G left right carrierF carrierG leftCont rightCont
      exact FpsSingletonEmptyHistoryClassifier_continuation_comm_closed carrierF carrierG
        leftCont rightCont
    · intro xs ys classified spine
      exact FpsSingletonCauchyProduct_classifier_congruence classified spine

end BEDC.Derived.FpsUp
