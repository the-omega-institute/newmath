import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CategoryHomCarrier_e1_source_e1_target_visible_morphism_iff {a r k : BHist} :
    CategoryHomCarrier (BHist.e1 a) (BHist.e1 r) (BHist.e1 k) ↔
      UnaryHistory a ∧ UnaryHistory k ∧ UnaryHistory r ∧ Cont (BHist.e1 a) k r := by
  constructor
  · intro homCarrier
    have data :=
      (CategoryHomCarrier_e1_morphism_target_iff
        (a := BHist.e1 a) (k := k) (r := r)).mp homCarrier
    exact
      And.intro (unary_e1_inversion data.left)
        (And.intro data.right.left
          (And.intro (unary_e1_inversion homCarrier.right.left) data.right.right))
  · intro data
    exact
      (CategoryHomCarrier_e1_morphism_target_iff
        (a := BHist.e1 a) (k := k) (r := r)).mpr
        (And.intro (unary_e1_closed data.left)
          (And.intro data.right.left data.right.right.right))

end BEDC.Derived.CategoryUp
