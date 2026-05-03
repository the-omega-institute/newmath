import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CategoryHomCarrier_empty_source_target_morphism_swap_iff {b f : BHist} :
    CategoryHomCarrier BHist.Empty b f <-> CategoryHomCarrier BHist.Empty f b := by
  constructor
  · intro homCarrier
    have data := (CategoryHomCarrier_empty_source_iff (b := b) (f := f)).mp homCarrier
    exact (CategoryHomCarrier_empty_source_iff (b := f) (f := b)).mpr
      (And.intro (unary_transport data.left (hsame_symm data.right)) (hsame_symm data.right))
  · intro homCarrier
    have data := (CategoryHomCarrier_empty_source_iff (b := f) (f := b)).mp homCarrier
    exact (CategoryHomCarrier_empty_source_iff (b := b) (f := f)).mpr
      (And.intro (unary_transport data.left (hsame_symm data.right)) (hsame_symm data.right))

end BEDC.Derived.CategoryUp
