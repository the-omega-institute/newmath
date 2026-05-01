import BEDC.Derived.ProdUp
import BEDC.Derived.RealUp

namespace BEDC.Derived.S1Up

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.ProdUp
open BEDC.Derived.RealUp
open BEDC.Derived.RatUp

def SOneHistoryCarrier (h : BHist) : Prop :=
  ProdHistoryCarrier RealConstantHistoryCarrier RealConstantHistoryCarrier h

theorem SOneHistoryCarrier_rational_components {h : BHist} :
    SOneHistoryCarrier h →
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

end BEDC.Derived.S1Up
