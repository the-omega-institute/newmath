import BEDC.Derived.CategoryUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

theorem IdentityFunctorCarrier_semanticNameCert {a : BHist} (objectCarrier : UnaryHistory a) :
    SemanticNameCert
      (fun f : BHist => CategoryHomCarrier a a f ∧ hsame f BHist.Empty)
      (fun f : BHist => CategoryHomCarrier a a f ∧ hsame f BHist.Empty)
      (fun f : BHist => CategoryHomCarrier a a f ∧ hsame f BHist.Empty)
      hsame := by
  constructor
  · constructor
    · exact Exists.intro BHist.Empty
        (And.intro (CategoryHomCarrier_empty_identity objectCarrier)
          (hsame_refl BHist.Empty))
    · intro f _carrier
      exact hsame_refl f
    · intro f g same
      exact hsame_symm same
    · intro f g r sameFG sameGR
      exact hsame_trans sameFG sameGR
    · intro f g same carrier
      exact And.intro
        (CategoryHomCarrier_hsame_transport (hsame_refl a) (hsame_refl a) same carrier.left)
        (hsame_trans (hsame_symm same) carrier.right)
  · intro f source
    exact source
  · intro f source
    exact source

end BEDC.Derived.FunctorUp
