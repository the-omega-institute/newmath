import BEDC.Derived.FieldUp
import BEDC.Derived.VecSpaceUp

namespace BEDC.Derived.ProjectiveSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
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

def ProjectiveSpaceSingletonPuncturedCarrier
    (rep scalar action : BHist) : Prop :=
  VecSpaceSingletonCarrier rep ∧ FieldSingletonCarrier scalar ∧
    Cont scalar rep action ∧ hsame action BHist.Empty

theorem ProjectiveSpaceSingletonPuncturedCarrier_obligation
    {rep scalar action : BHist} :
    VecSpaceSingletonCarrier rep -> FieldSingletonCarrier scalar ->
      Cont scalar rep action -> ProjectiveSpaceSingletonPuncturedCarrier rep scalar action := by
  intro repCarrier scalarCarrier actionCont
  constructor
  · exact repCarrier
  · constructor
    · exact scalarCarrier
    · constructor
      · exact actionCont
      · cases repCarrier
        cases scalarCarrier
        cases actionCont
        exact hsame_refl BHist.Empty

def ProjectiveSpaceSingletonScalingOrbitClassifier
    (repA scalarA actionA repB scalarB actionB : BHist) : Prop :=
  ProjectiveSpaceSingletonPuncturedCarrier repA scalarA actionA ∧
    ProjectiveSpaceSingletonPuncturedCarrier repB scalarB actionB ∧ hsame repA repB

theorem ProjectiveSpaceSingletonScalingOrbitClassifier_obligation
    {repA scalarA actionA repB scalarB actionB repC scalarC actionC : BHist} :
    ProjectiveSpaceSingletonPuncturedCarrier repA scalarA actionA ->
      ProjectiveSpaceSingletonPuncturedCarrier repB scalarB actionB ->
        ProjectiveSpaceSingletonPuncturedCarrier repC scalarC actionC ->
          Cont scalarA repA actionA ∧ Cont scalarB repB actionB ∧
            ProjectiveSpaceSingletonScalingOrbitClassifier
              repA scalarA actionA repA scalarA actionA ∧
            ProjectiveSpaceSingletonScalingOrbitClassifier
              repA scalarA actionA repB scalarB actionB ∧
            ProjectiveSpaceSingletonScalingOrbitClassifier
              repB scalarB actionB repA scalarA actionA ∧
            ProjectiveSpaceSingletonScalingOrbitClassifier
              repA scalarA actionA repC scalarC actionC := by
  intro carrierA carrierB carrierC
  have sameAB : hsame repA repB :=
    hsame_trans carrierA.left (hsame_symm carrierB.left)
  have sameBA : hsame repB repA :=
    hsame_symm sameAB
  have sameAC : hsame repA repC :=
    hsame_trans carrierA.left (hsame_symm carrierC.left)
  constructor
  · exact carrierA.right.right.left
  · constructor
    · exact carrierB.right.right.left
    · constructor
      · exact And.intro carrierA (And.intro carrierA (hsame_refl repA))
      · constructor
        · exact And.intro carrierA (And.intro carrierB sameAB)
        · constructor
          · exact And.intro carrierB (And.intro carrierA sameBA)
          · exact And.intro carrierA (And.intro carrierC sameAC)

end BEDC.Derived.ProjectiveSpaceUp
