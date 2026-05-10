import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CategoryUp_mature_host_interface_inventory {a b c f g fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory c ∧ UnaryHistory f ∧
        UnaryHistory g ∧ UnaryHistory fg ∧ CategoryHomCarrier a c fg ∧
          hsame fg (append f g) := by
  intro left right comp
  have composite : CategoryHomCarrier a c fg :=
    CategoryHomCarrier_comp_closed left right comp
  exact And.intro left.left
    (And.intro left.right.left
      (And.intro right.right.left
        (And.intro left.right.right.left
          (And.intro right.right.right.left
            (And.intro composite.right.right.left
              (And.intro composite comp))))))

end BEDC.Derived.CategoryUp
