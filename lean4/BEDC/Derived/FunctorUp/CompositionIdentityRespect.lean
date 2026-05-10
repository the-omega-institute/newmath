import BEDC.Derived.FunctorUp.FamilyReadback

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist

theorem FunctorComposition_identity_sameness_respect_required :
    RawFunctorIdentityPreserving RawFunctorObjectMap RawFunctorMorphismMap ∧
      (hsame (RawFunctorMorphismMap BHist.Empty)
          (RawFunctorMorphismMap (BHist.e1 BHist.Empty)) -> False) := by
  constructor
  · constructor
    · exact hsame_refl BHist.Empty
    · constructor
      · exact hsame_refl (BHist.e1 BHist.Empty)
      · constructor
        · exact hsame_refl BHist.Empty
        · exact hsame_refl (BHist.e1 BHist.Empty)
  · intro same
    exact not_hsame_emp_e1 same

end BEDC.Derived.FunctorUp
