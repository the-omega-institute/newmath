import BEDC.Derived.FunctorUp

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

theorem FunctorPrefixHomCarrier_empty_morphism_source_iff {p a source : BHist} :
    CategoryHomCarrier source (append p a) BHist.Empty ↔
      UnaryHistory p ∧ UnaryHistory a ∧ hsame source (append p a) := by
  constructor
  · intro homCarrier
    have identityData :=
      (CategoryHomCarrier_empty_identity_iff (a := source) (b := append p a)).mp
        homCarrier
    exact
      And.intro (unary_append_left_factor identityData.right.left)
        (And.intro (unary_append_right_factor identityData.right.left)
          identityData.right.right)
  · intro data
    have targetCarrier : UnaryHistory (append p a) :=
      unary_append_closed data.left data.right.left
    exact
      (CategoryHomCarrier_empty_identity_iff (a := source) (b := append p a)).mpr
        (And.intro
          (unary_transport targetCarrier (hsame_symm data.right.right))
          (And.intro targetCarrier data.right.right))

end BEDC.Derived.FunctorUp
