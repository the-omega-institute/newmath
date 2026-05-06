import BEDC.Derived.GroupUp
import BEDC.Derived.ManifoldUp
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.LieGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.ManifoldUp

theorem LieGroupSingletonOperation_smoothness {x y product inverse transition : BHist} :
    GroupSingletonCarrier x -> GroupSingletonCarrier y -> ManifoldSingletonCarrier x ->
      ManifoldSingletonCarrier y -> Cont x y product -> Cont product BHist.Empty inverse ->
        Cont product inverse transition ->
          GroupSingletonClassifier product inverse ∧ ManifoldSingletonCarrier product ∧
            ManifoldSingletonCarrier inverse ∧ hsame transition BHist.Empty ∧
              UnaryHistory transition := by
  intro carrierX carrierY _manifoldX _manifoldY productRow inverseRow transitionRow
  have productEmpty : hsame product BHist.Empty :=
    cont_respects_hsame carrierX carrierY productRow (cont_left_unit BHist.Empty)
  have inverseProduct : hsame inverse product :=
    cont_right_unit_result inverseRow
  have inverseEmpty : hsame inverse BHist.Empty :=
    hsame_trans inverseProduct productEmpty
  have transitionEmpty : hsame transition BHist.Empty :=
    cont_respects_hsame productEmpty inverseEmpty transitionRow (cont_left_unit BHist.Empty)
  have classified : GroupSingletonClassifier product inverse :=
    And.intro productEmpty
      (And.intro inverseEmpty (hsame_trans productEmpty (hsame_symm inverseEmpty)))
  have transitionUnary : UnaryHistory transition :=
    unary_transport unary_empty (hsame_symm transitionEmpty)
  exact And.intro classified
    (And.intro productEmpty (And.intro inverseEmpty (And.intro transitionEmpty transitionUnary)))

end BEDC.Derived.LieGroupUp
