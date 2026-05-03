import BEDC.Derived.FunctorUp

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

theorem FunctorPrefixHomCarrier_right_unary_tail_comp_public_readback
    {p a b f q r : BHist} :
    CategoryHomCarrier (append p a) (append p b) f -> UnaryHistory q -> Cont f q r ->
      CategoryHomCarrier (append p a) (append p (append b q)) r ∧
        (∀ {r' : BHist}, Cont f q r' ->
          CategoryHomCarrier (append p a) (append p (append b q)) r' -> hsame r r') := by
  intro left qCarrier tailRel
  have right : CategoryHomCarrier (append p b) (append (append p b) q) q :=
    And.intro left.right.left
      (And.intro (unary_append_closed left.right.left qCarrier)
        (And.intro qCarrier (cont_intro rfl)))
  have rawComposite : CategoryHomCarrier (append p a) (append (append p b) q) r :=
    CategoryHomCarrier_comp_closed left right tailRel
  have composite : CategoryHomCarrier (append p a) (append p (append b q)) r :=
    CategoryHomCarrier_hsame_transport (hsame_refl (append p a)) (append_assoc p b q)
      (hsame_refl r) rawComposite
  exact And.intro composite
    (fun {_r'} _tailRel' displayed =>
      CategoryHomCarrier_morphism_deterministic composite displayed)

end BEDC.Derived.FunctorUp
