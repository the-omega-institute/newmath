import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist

theorem CategoryHomCarrier_e1_target_morphism_exactness_iff {a k r : BHist} :
    CategoryHomCarrier a (BHist.e1 r) (BHist.e1 k) <-> CategoryHomCarrier a r k := by
  constructor
  · exact CategoryHomCarrier_e1_target_morphism_exactness
  · intro homCarrier
    exact
      (CategoryHomCarrier_e1_morphism_target_iff (a := a) (k := k) (r := r)).mpr
        ⟨homCarrier.left, homCarrier.right.right.left, homCarrier.right.right.right⟩

end BEDC.Derived.CategoryUp
