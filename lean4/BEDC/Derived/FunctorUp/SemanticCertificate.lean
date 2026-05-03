import BEDC.Derived.FunctorUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

theorem FunctorPrefixHomCarrier_comp_result_semanticNameCert {p a b c f g fg : BHist}
    (prefixCarrier : UnaryHistory p) (left : CategoryHomCarrier a b f)
    (right : CategoryHomCarrier b c g) (comp : Cont f g fg) :
    SemanticNameCert
      (fun h : BHist => CategoryHomCarrier (append p a) (append p c) h ∧ hsame h fg)
      (fun h : BHist => CategoryHomCarrier (append p a) (append p c) h ∧ hsame h fg)
      (fun h : BHist => CategoryHomCarrier (append p a) (append p c) h ∧ hsame h fg)
      hsame := by
  constructor
  · constructor
    · exact Exists.intro fg
        (And.intro
          (FunctorPrefixHomCarrier_comp_preserves prefixCarrier left right comp)
          (hsame_refl fg))
    · intro h _carrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same carrier
      exact And.intro
        (CategoryHomCarrier_hsame_transport (hsame_refl (append p a)) (hsame_refl (append p c))
          same carrier.left)
        (hsame_trans (hsame_symm same) carrier.right)
  · intro h source
    exact source
  · intro h source
    exact source

end BEDC.Derived.FunctorUp
