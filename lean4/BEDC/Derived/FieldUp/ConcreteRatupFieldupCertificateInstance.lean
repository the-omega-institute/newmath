import BEDC.Derived.FieldUp.FieldCertificateObligations

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem ConcreteRatupFieldupCertificateInstance :
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
  have ratCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    RatHistoryCarrier_e1_tail_unary_iff.mpr unary_empty
  have ratClassifier :
      RatHistoryClassifier (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
    ⟨ratCarrier, ratCarrier, hsame_refl (BHist.e1 BHist.Empty)⟩
  have denomCarrier : RatDenomUnitCarrier BHist.Empty :=
    Or.inl (hsame_refl BHist.Empty)
  have denomClassifier : RatDenomUnitClassifier BHist.Empty BHist.Empty :=
    ⟨denomCarrier, denomCarrier, hsame_refl BHist.Empty⟩
  exact
    ⟨ratCarrier, ratClassifier, denomCarrier, denomClassifier,
      hsame_refl (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty)),
      hsame_refl (append BHist.Empty BHist.Empty),
      hsame_refl (append BHist.Empty BHist.Empty),
      hsame_refl
        (append (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty))
          (append BHist.Empty BHist.Empty))⟩

end BEDC.Derived.FieldUp
