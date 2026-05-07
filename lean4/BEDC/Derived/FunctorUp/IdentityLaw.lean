import BEDC.Derived.CategoryUp.IdentityLaw
import BEDC.Derived.FunctorUp
import BEDC.Derived.FunctorUp.PrefixCarrier

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

theorem FunctorPrefixHomCarrier_two_sided_identity_law {p a b f left right : BHist} :
    UnaryHistory p -> CategoryHomCarrier a b f -> Cont BHist.Empty f left ->
      Cont f BHist.Empty right ->
        CategoryHomCarrier (append p a) (append p b) left ∧
          CategoryHomCarrier (append p a) (append p b) right ∧ hsame left f ∧
            hsame right f ∧ hsame left right := by
  intro prefixCarrier homCarrier leftRel rightRel
  exact
    CategoryHomCarrier_two_sided_identity_law
      (FunctorPrefixHomCarrier_preserves prefixCarrier homCarrier) leftRel rightRel

theorem PrefixFunctorCarrier_empty_prefix_identity_unit_laws {p a b f left right : BHist} :
    PrefixFunctorCarrier p -> CategoryHomCarrier a b f -> Cont BHist.Empty f left ->
      Cont f BHist.Empty right ->
        CategoryHomCarrier (append BHist.Empty (append p a))
            (append BHist.Empty (append p b)) left ∧
          CategoryHomCarrier (append p a) (append p b) right ∧ hsame left f ∧
            hsame right f ∧ hsame left right := by
  intro prefixCarrier homCarrier leftRel rightRel
  have prefixedCarrier : CategoryHomCarrier (append p a) (append p b) f :=
    prefixCarrier.hom_preserves homCarrier
  have identityClosed :=
    CategoryHomCarrier_identity_square_closed prefixedCarrier leftRel rightRel
  have leftEmptyTransport :
      CategoryHomCarrier (append BHist.Empty (append p a))
        (append BHist.Empty (append p b)) left :=
    CategoryHomCarrier_hsame_transport
      (hsame_symm (append_empty_left (append p a)))
      (hsame_symm (append_empty_left (append p b)))
      (hsame_refl left)
      identityClosed.left
  exact
    And.intro leftEmptyTransport
      (And.intro identityClosed.right.left
        (And.intro
          (cont_left_unit_result leftRel)
          (And.intro
            (cont_deterministic rightRel (cont_right_unit f))
            identityClosed.right.right)))

end BEDC.Derived.FunctorUp
