import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CategoryUp_StdBridge {a b c f g fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory c ∧ CategoryHomCarrier a b f ∧
        CategoryHomCarrier b c g ∧ CategoryHomCarrier a c fg ∧
          SemanticNameCert
            (fun h : BHist => CategoryHomCarrier a c h ∧ hsame h fg)
            (fun h : BHist => CategoryHomCarrier a c h ∧ hsame h fg)
            (fun h : BHist => CategoryHomCarrier a c h ∧ hsame h fg)
            hsame := by
  intro left right comp
  have composite : CategoryHomCarrier a c fg :=
    CategoryHomCarrier_comp_closed left right comp
  have cert :
      SemanticNameCert
        (fun h : BHist => CategoryHomCarrier a c h ∧ hsame h fg)
        (fun h : BHist => CategoryHomCarrier a c h ∧ hsame h fg)
        (fun h : BHist => CategoryHomCarrier a c h ∧ hsame h fg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro fg (And.intro composite (hsame_refl fg))
      equiv_refl := by
        intro h _source
        exact hsame_refl h
      equiv_symm := by
        intro h k same
        exact hsame_symm same
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k same source
        exact And.intro
          (CategoryHomCarrier_hsame_transport (hsame_refl a) (hsame_refl c) same source.left)
          (hsame_trans (hsame_symm same) source.right)
    }
    pattern_sound := by
      intro _h source
      exact source
    ledger_sound := by
      intro _h source
      exact source
  }
  exact And.intro left.left
    (And.intro left.right.left
      (And.intro right.right.left
        (And.intro left
          (And.intro right
            (And.intro composite cert)))))

end BEDC.Derived.CategoryUp
