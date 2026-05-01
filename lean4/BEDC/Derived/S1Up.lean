import BEDC.Derived.ProdUp
import BEDC.Derived.RatUp
import BEDC.Derived.RealUp

namespace BEDC.Derived.S1Up

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.ProdUp
open BEDC.Derived.RatUp
open BEDC.Derived.RealUp

def SOneUnitHistory : BHist := BHist.e1 (BHist.e1 BHist.Empty)

def SOneProductHistoryCarrier (h : BHist) : Prop :=
  ProdHistoryCarrier RealConstantHistoryCarrier RealConstantHistoryCarrier h

def SOneHistoryCarrier (x y equation point : BHist) : Prop :=
  RealConstantHistoryCarrier x ∧ RealConstantHistoryCarrier y ∧
    RealConstantHistoryClassifier equation SOneUnitHistory ∧ Cont x y point

theorem SOneHistoryCarrier_rational_components {h : BHist} :
    SOneProductHistoryCarrier h →
      ∃ x y dx dy : BHist,
        hsame x (BHist.e1 dx) ∧ RatHistoryCarrier dx ∧
          hsame y (BHist.e1 dy) ∧ RatHistoryCarrier dy ∧ Cont x y h := by
  intro carrier
  cases carrier with
  | intro x restX =>
      cases restX with
      | intro y data =>
          cases data with
          | intro xCarrier rest =>
              cases rest with
              | intro yCarrier cont =>
                  cases xCarrier with
                  | intro dx xData =>
                      cases xData with
                      | intro sameX dxCarrier =>
                          cases yCarrier with
                          | intro dy yData =>
                              cases yData with
                              | intro sameY dyCarrier =>
                                  exact Exists.intro x
                                    (Exists.intro y
                                      (Exists.intro dx
                                        (Exists.intro dy
                                          (And.intro sameX
                                            (And.intro dxCarrier
                                              (And.intro sameY
                                                (And.intro dyCarrier cont)))))))

theorem SOneHistoryCarrier_real_pair {x y equation point : BHist} :
    SOneHistoryCarrier x y equation point ->
      ProdHistoryCarrier RealConstantHistoryCarrier RealConstantHistoryCarrier point := by
  intro carrier
  cases carrier with
  | intro xCarrier rest =>
      cases rest with
      | intro yCarrier rest =>
          cases rest with
          | intro _equationCarrier pointCont =>
              exact ProdHistoryCarrier_cont_intro xCarrier yCarrier pointCont

theorem SOneHistoryCarrier_point_deterministic
    {x y equation equation' point point' : BHist} :
    SOneHistoryCarrier x y equation point ->
      SOneHistoryCarrier x y equation' point' -> hsame point point' := by
  intro left right
  exact cont_deterministic left.right.right.right right.right.right.right

theorem SOneHistoryCarrier_rational_unit_components {x y equation point : BHist} :
    SOneHistoryCarrier x y equation point →
      ∃ dx dy : BHist,
        hsame x (BHist.e1 dx) ∧ RatHistoryCarrier dx ∧
          hsame y (BHist.e1 dy) ∧ RatHistoryCarrier dy ∧
            RealConstantHistoryClassifier equation SOneUnitHistory ∧ Cont x y point := by
  intro carrier
  cases carrier with
  | intro xCarrier rest =>
      cases rest with
      | intro yCarrier rest =>
          cases rest with
          | intro equationCarrier pointCont =>
              cases xCarrier with
              | intro dx xData =>
                  cases xData with
                  | intro sameX dxCarrier =>
                      cases yCarrier with
                      | intro dy yData =>
                          cases yData with
                          | intro sameY dyCarrier =>
                              exact Exists.intro dx
                                (Exists.intro dy
                                  (And.intro sameX
                                    (And.intro dxCarrier
                                      (And.intro sameY
                                        (And.intro dyCarrier
                                          (And.intro equationCarrier pointCont))))))

theorem SOneHistoryCarrier_equation_witness_transport
    {x y equation equation' point : BHist} :
    SOneHistoryCarrier x y equation point -> hsame equation equation' ->
      SOneHistoryCarrier x y equation' point := by
  intro carrier sameEquation
  cases carrier with
  | intro xCarrier rest =>
      cases rest with
      | intro yCarrier rest =>
          cases rest with
          | intro equationCarrier pointCont =>
              exact
                And.intro xCarrier
                  (And.intro yCarrier
                    (And.intro
                      (RealConstantHistoryClassifier_endpoint_transport sameEquation
                        (hsame_refl SOneUnitHistory) equationCarrier)
                      pointCont))

theorem SOneHistoryCarrier_coordinate_transport
    {x y equation point x' y' equation' point' : BHist} :
    SOneHistoryCarrier x y equation point -> hsame x x' -> hsame y y' ->
      hsame equation equation' -> hsame point point' ->
        SOneHistoryCarrier x' y' equation' point' := by
  intro carrier sameX sameY sameEquation samePoint
  cases carrier with
  | intro xCarrier rest =>
      cases rest with
      | intro yCarrier rest =>
          cases rest with
          | intro equationCarrier pointCont =>
              have xCarrier' : RealConstantHistoryCarrier x' := by
                cases sameX
                exact xCarrier
              have yCarrier' : RealConstantHistoryCarrier y' := by
                cases sameY
                exact yCarrier
              have equationCarrier' :
                  RealConstantHistoryClassifier equation' SOneUnitHistory := by
                exact RealConstantHistoryClassifier_endpoint_transport sameEquation
                  (hsame_refl SOneUnitHistory) equationCarrier
              have pointCont' : Cont x' y' point' := by
                cases sameX
                cases sameY
                exact cont_result_hsame_transport pointCont samePoint
              exact And.intro xCarrier'
                (And.intro yCarrier' (And.intro equationCarrier' pointCont'))

theorem SOneHistoryCarrier_component_classifier_ledger_determinacy
    {x y e p x' y' e' p' : BHist} :
    SOneHistoryCarrier x y e p -> SOneHistoryCarrier x' y' e' p' ->
      hsame x x' -> hsame y y' -> hsame e e' ∧ hsame p p' := by
  intro left right sameX sameY
  cases left with
  | intro _leftX leftRest =>
      cases leftRest with
      | intro _leftY leftRest =>
          cases leftRest with
          | intro leftEquation leftPoint =>
              cases right with
              | intro _rightX rightRest =>
                  cases rightRest with
                  | intro _rightY rightRest =>
                      cases rightRest with
                      | intro rightEquation rightPoint =>
                          have leftEquationUnit : hsame e SOneUnitHistory := by
                            cases leftEquation with
                            | intro d leftData =>
                                cases leftData with
                                | intro q leftData =>
                                    cases leftData with
                                    | intro sameE leftData =>
                                        cases leftData with
                                        | intro sameUnit ratClassifier =>
                                            exact hsame_trans sameE
                                              (hsame_trans
                                                (hsame_e1_congr ratClassifier.right.right)
                                                (hsame_symm sameUnit))
                          have rightEquationUnit : hsame e' SOneUnitHistory := by
                            cases rightEquation with
                            | intro d rightData =>
                                cases rightData with
                                | intro q rightData =>
                                    cases rightData with
                                    | intro sameE rightData =>
                                        cases rightData with
                                        | intro sameUnit ratClassifier =>
                                            exact hsame_trans sameE
                                              (hsame_trans
                                                (hsame_e1_congr ratClassifier.right.right)
                                                (hsame_symm sameUnit))
                          exact And.intro
                            (hsame_trans leftEquationUnit (hsame_symm rightEquationUnit))
                            (cont_respects_hsame sameX sameY leftPoint rightPoint)

end BEDC.Derived.S1Up
