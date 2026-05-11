import BEDC.Derived.FieldExtUp

namespace BEDC.Derived.FieldExtUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.FieldUp
open BEDC.Derived.VecSpaceUp

theorem FieldExtSingleton_empty_history_instance_surface :
    FieldExtSingletonCarrier BHist.Empty ∧ FieldSingletonCarrier BHist.Empty ∧
      VecSpaceSingletonCarrier BHist.Empty ∧
        FieldExtSingletonClassifier BHist.Empty BHist.Empty ∧
          Cont BHist.Empty BHist.Empty BHist.Empty := by
  have emptyField : FieldSingletonCarrier BHist.Empty :=
    hsame_refl BHist.Empty
  have emptyVec : VecSpaceSingletonCarrier BHist.Empty :=
    hsame_refl BHist.Empty
  have emptyExt : FieldExtSingletonCarrier BHist.Empty :=
    And.intro emptyField emptyVec
  have fieldClassified : FieldSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyField (And.intro emptyField (hsame_refl BHist.Empty))
  have vecClassified : VecSpaceSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyVec (And.intro emptyVec (hsame_refl BHist.Empty))
  have extClassified : FieldExtSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro fieldClassified vecClassified
  exact And.intro emptyExt
    (And.intro emptyField (And.intro emptyVec (And.intro extClassified rfl)))

end BEDC.Derived.FieldExtUp
