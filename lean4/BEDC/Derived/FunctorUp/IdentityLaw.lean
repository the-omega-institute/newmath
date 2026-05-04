import BEDC.Derived.CategoryUp.IdentityLaw
import BEDC.Derived.FunctorUp

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

end BEDC.Derived.FunctorUp
