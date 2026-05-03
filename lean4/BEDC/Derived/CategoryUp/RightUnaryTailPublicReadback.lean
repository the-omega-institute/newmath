import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CategoryHomCarrier_right_unary_tail_comp_public_readback {a b f q r : BHist} :
    CategoryHomCarrier a b f -> UnaryHistory q -> Cont f q r ->
      CategoryHomCarrier a (append b q) r ∧
        (∀ {r' : BHist}, Cont f q r' -> CategoryHomCarrier a (append b q) r' ->
          hsame r r') := by
  intro left qCarrier tailRel
  have right : CategoryHomCarrier b (append b q) q :=
    And.intro left.right.left
      (And.intro (unary_append_closed left.right.left qCarrier)
        (And.intro qCarrier (cont_intro rfl)))
  have composite : CategoryHomCarrier a (append b q) r :=
    CategoryHomCarrier_comp_closed left right tailRel
  exact And.intro composite
    (fun {_r'} _tailRel' displayed =>
      CategoryHomCarrier_morphism_deterministic composite displayed)

end BEDC.Derived.CategoryUp
