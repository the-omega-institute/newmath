import BEDC.Derived.FieldUp.ConcreteExitObject
import BEDC.Derived.FieldUp.ConcreteRatupFieldupCertificateInstance

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RatupFieldupExitCertificateNontrivialSupportNeutral :
    RatHistoryCarrier (BHist.e1 BHist.Empty) ∧
      (hsame (BHist.e1 BHist.Empty) BHist.Empty -> False) ∧
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
            (append BHist.Empty BHist.Empty)) ∧
          RatupFieldupConcreteExitObject
            (BHist.e1 BHist.Empty)
            BHist.Empty
            (BHist.e1 BHist.Empty)
            BHist.Empty
            BHist.Empty
            (BHist.e1 BHist.Empty)
            (BHist.e1 BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist Cont hsame RatHistoryCarrier RatDenomUnitCarrier
  have ratCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    RatHistoryCarrier_e1_tail_unary_iff.mpr unary_empty
  have nonempty : hsame (BHist.e1 BHist.Empty) BHist.Empty -> False := by
    intro sameEmpty
    exact RatHistoryCarrier_not_empty ratCarrier sameEmpty
  have obligations :
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
          (append BHist.Empty BHist.Empty)) :=
    ConcreteRatupFieldupCertificateInstance
  have denomCarrier : RatDenomUnitCarrier BHist.Empty :=
    Or.inl (hsame_refl BHist.Empty)
  have ratClassifier :
      RatHistoryClassifier (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
    ⟨ratCarrier, ratCarrier, hsame_refl (BHist.e1 BHist.Empty)⟩
  have denomClassifier : RatDenomUnitClassifier BHist.Empty BHist.Empty :=
    ⟨denomCarrier, denomCarrier, hsame_refl BHist.Empty⟩
  have contextCarrier : Cont BHist.Empty (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
    cont_left_unit (BHist.e1 BHist.Empty)
  have selectorDenominator :
      Cont (BHist.e1 BHist.Empty) BHist.Empty (BHist.e1 BHist.Empty) :=
    cont_right_unit (BHist.e1 BHist.Empty)
  have exitObject :
      RatupFieldupConcreteExitObject
        (BHist.e1 BHist.Empty)
        BHist.Empty
        (BHist.e1 BHist.Empty)
        BHist.Empty
        BHist.Empty
        (BHist.e1 BHist.Empty)
        (BHist.e1 BHist.Empty) :=
    ⟨ratCarrier, denomCarrier, ratClassifier, denomClassifier, contextCarrier,
      selectorDenominator, hsame_refl (BHist.e1 BHist.Empty)⟩
  exact ⟨ratCarrier, nonempty, obligations, exitObject⟩

end BEDC.Derived.FieldUp
