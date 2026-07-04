import BEDC.Derived.FieldUp.ConcreteExitObject
import BEDC.Derived.FieldUp.ConcreteRatupFieldupCertificateInstance

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RatupFieldupProductClassifierAndNonzeroExitPackage :
    RatHistoryClassifier (append (BHist.e1 BHist.Empty) BHist.Empty)
        (BHist.e1 BHist.Empty) ∧
      RatDenomUnitClassifier BHist.Empty BHist.Empty ∧
        RatupFieldupConcreteExitObject (BHist.e1 BHist.Empty) BHist.Empty
            (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty (BHist.e1 BHist.Empty)
            (BHist.e1 BHist.Empty) ∧
          FieldCertificateObligations
            (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty))
            (BHist.e1 BHist.Empty)
            (BHist.e1 BHist.Empty)
            (append BHist.Empty BHist.Empty)
            BHist.Empty
            BHist.Empty
            BHist.Empty
            BHist.Empty
            (append BHist.Empty BHist.Empty)
            BHist.Empty
            (append (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty))
              (append BHist.Empty BHist.Empty)) := by
  -- BEDC touchpoint anchor: BHist Cont hsame RatHistoryCarrier RatDenomUnitCarrier
  have ratCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    RatHistoryCarrier_e1_tail_unary_iff.mpr unary_empty
  have tailClassifier :
      RatHistoryClassifier (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
    ⟨ratCarrier, ratCarrier, hsame_refl (BHist.e1 BHist.Empty)⟩
  have productClassifier :
      RatHistoryClassifier (append (BHist.e1 BHist.Empty) BHist.Empty)
        (BHist.e1 BHist.Empty) :=
    RatHistoryClassifier_hsame_transport (append_empty_right (BHist.e1 BHist.Empty))
      (hsame_refl (BHist.e1 BHist.Empty)) tailClassifier
  have denomCarrier : RatDenomUnitCarrier BHist.Empty :=
    Or.inl (hsame_refl BHist.Empty)
  have denomClassifier : RatDenomUnitClassifier BHist.Empty BHist.Empty :=
    ⟨denomCarrier, denomCarrier, hsame_refl BHist.Empty⟩
  have contextCarrier : Cont BHist.Empty (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
    cont_left_unit (BHist.e1 BHist.Empty)
  have selectorDenominator :
      Cont (BHist.e1 BHist.Empty) BHist.Empty (BHist.e1 BHist.Empty) :=
    cont_right_unit (BHist.e1 BHist.Empty)
  have exitObject :
      RatupFieldupConcreteExitObject (BHist.e1 BHist.Empty) BHist.Empty
        (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty (BHist.e1 BHist.Empty)
        (BHist.e1 BHist.Empty) :=
    (RatupFieldupConcreteExitObjectComplete ratCarrier denomCarrier tailClassifier
      denomClassifier contextCarrier selectorDenominator).left
  exact
    ⟨productClassifier, denomClassifier, exitObject, ConcreteRatupFieldupCertificateInstance⟩

end BEDC.Derived.FieldUp
