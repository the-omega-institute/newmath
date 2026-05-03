import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

theorem CategoryHomCarrier_comp_tail_semanticNameCert {a b c f g fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      SemanticNameCert
        (fun t : BHist => CategoryHomCarrier a c t ∧ hsame t fg)
        (fun t : BHist => CategoryHomCarrier a c t ∧ hsame t fg)
        (fun t : BHist => CategoryHomCarrier a c t ∧ hsame t fg)
        hsame := by
  intro left right comp
  constructor
  · constructor
    · exact Exists.intro fg
        (And.intro (CategoryHomCarrier_comp_closed left right comp) (hsame_refl fg))
    · intro h _carrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same carrier
      exact And.intro
        (CategoryHomCarrier_hsame_transport (hsame_refl a) (hsame_refl c) same carrier.left)
        (hsame_trans (hsame_symm same) carrier.right)
  · intro h source
    exact source
  · intro h source
    exact source

end BEDC.Derived.CategoryUp
