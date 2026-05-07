import BEDC.Derived.FieldUp
import BEDC.Derived.VecSpaceUp

namespace BEDC.Derived.ProjectiveSpaceUp

open BEDC.FKernel.Hist
open BEDC.Derived.FieldUp
open BEDC.Derived.VecSpaceUp

def ProjectiveSpacePuncturedCarrier (v scalar action : BHist) : Prop :=
  VecSpaceSingletonCarrier v ∧
    FieldSingletonNonZero scalar ∧
      VecSpaceSingletonClassifier (VecSpaceSingletonSmul scalar v) action

theorem ProjectiveSpacePuncturedCarrier_obligation {v scalar action : BHist} :
    VecSpaceSingletonCarrier v ->
      FieldSingletonNonZero scalar ->
        VecSpaceSingletonClassifier (VecSpaceSingletonSmul scalar v) action ->
          ProjectiveSpacePuncturedCarrier v scalar action ∧
            (hsame scalar BHist.Empty -> False) := by
  intro vectorCarrier scalarNonzero actionClassified
  constructor
  · exact And.intro vectorCarrier (And.intro scalarNonzero actionClassified)
  · intro scalarEmpty
    exact not_hsame_emp_e0 (hsame_trans (hsame_symm scalarEmpty) scalarNonzero.right)

end BEDC.Derived.ProjectiveSpaceUp
