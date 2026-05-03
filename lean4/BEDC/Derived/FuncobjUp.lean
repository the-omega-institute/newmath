import BEDC.Derived.FunctorUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.FuncobjUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp
open BEDC.Derived.FunctorUp

theorem FuncobjPointwiseHomCarrier_semanticNameCert {p a b f : BHist}
    (prefixCarrier : UnaryHistory p) (hom : CategoryHomCarrier a b f) :
    SemanticNameCert
      (fun t : BHist =>
        CategoryHomCarrier a b t ∧ CategoryHomCarrier (append p a) (append p b) t)
      (fun t : BHist =>
        CategoryHomCarrier a b t ∧ CategoryHomCarrier (append p a) (append p b) t)
      (fun t : BHist =>
        CategoryHomCarrier a b t ∧ CategoryHomCarrier (append p a) (append p b) t)
      hsame := by
  constructor
  · constructor
    · exact Exists.intro f
        (And.intro hom (FunctorPrefixHomCarrier_preserves prefixCarrier hom))
    · intro h _carrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same carrier
      exact And.intro
        (CategoryHomCarrier_hsame_transport (hsame_refl a) (hsame_refl b) same carrier.left)
        (CategoryHomCarrier_hsame_transport (hsame_refl (append p a))
          (hsame_refl (append p b)) same carrier.right)
  · intro h source
    exact source
  · intro h source
    exact source

end BEDC.Derived.FuncobjUp
