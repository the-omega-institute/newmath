import BEDC.Derived.FunctorUp
import BEDC.Derived.FunctorUp.PrefixCarrier
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

theorem PrefixFunctorCarrier_semanticNameCert {p : BHist} (prefixCarrier : UnaryHistory p) :
    SemanticNameCert (fun q : BHist => PrefixFunctorCarrier q ∧ hsame q p)
      (fun q : BHist => PrefixFunctorCarrier q ∧ hsame q p)
      (fun q : BHist => PrefixFunctorCarrier q ∧ hsame q p) hsame := by
  constructor
  · constructor
    · exact Exists.intro p
        (And.intro
          (BEDC.Derived.FunctorUp.PrefixFunctorCarrier_from_unary_prefix prefixCarrier)
          (hsame_refl p))
    · intro q _carrier
      exact hsame_refl q
    · intro q r same
      exact hsame_symm same
    · intro q r s sameQR sameRS
      exact hsame_trans sameQR sameRS
    · intro q r same carrier
      constructor
      · cases same
        exact carrier.left
      · exact hsame_trans (hsame_symm same) carrier.right
  · intro q source
    exact source
  · intro q source
    exact source

theorem FunctorPrefixIdentityCarrier_semanticNameCert {a b f : BHist}
    (homCarrier : CategoryHomCarrier a b f) :
    SemanticNameCert
      (fun h : BHist =>
        CategoryHomCarrier (append BHist.Empty a) (append BHist.Empty b) h ∧ hsame h f)
      (fun h : BHist =>
        CategoryHomCarrier (append BHist.Empty a) (append BHist.Empty b) h ∧ hsame h f)
      (fun h : BHist =>
        CategoryHomCarrier (append BHist.Empty a) (append BHist.Empty b) h ∧ hsame h f)
      hsame := by
  have identityPreserves :
      CategoryHomCarrier (append BHist.Empty a) (append BHist.Empty b) f :=
    FunctorPrefixHomCarrier_preserves unary_empty homCarrier
  constructor
  · constructor
    · exact Exists.intro f (And.intro identityPreserves (hsame_refl f))
    · intro h _carrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same carrier
      exact And.intro
        (CategoryHomCarrier_hsame_transport
          (hsame_refl (append BHist.Empty a))
          (hsame_refl (append BHist.Empty b))
          same
          carrier.left)
        (hsame_trans (hsame_symm same) carrier.right)
  · intro h source
    exact source
  · intro h source
    exact source

end BEDC.Derived.FunctorUp
