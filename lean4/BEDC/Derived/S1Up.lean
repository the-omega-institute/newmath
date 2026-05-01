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

end BEDC.Derived.S1Up
