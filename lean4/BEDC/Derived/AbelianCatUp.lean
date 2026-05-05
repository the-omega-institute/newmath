import BEDC.Derived.CategoryUp
import BEDC.Derived.GroupUp

namespace BEDC.Derived.AbelianCatUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp
open BEDC.Derived.GroupUp

def AbelianCatKernelCokernelCarrier
    (obj hom zero biprod add kernel cokernel factor : BHist) : Prop :=
  UnaryHistory obj ∧
    UnaryHistory hom ∧
      CategoryHomCarrier obj obj hom ∧
        GroupSingletonCarrier zero ∧
          Cont BHist.Empty hom biprod ∧
            Cont hom BHist.Empty add ∧
              Cont hom zero kernel ∧ Cont zero hom cokernel ∧ Cont kernel cokernel factor

theorem AbelianCatKernelCokernelCarrier_factorization_rows
    {obj hom zero biprod add kernel cokernel factor : BHist} :
    AbelianCatKernelCokernelCarrier obj hom zero biprod add kernel cokernel factor ->
      CategoryHomCarrier obj obj hom ∧
        Cont hom zero kernel ∧
          Cont zero hom cokernel ∧ Cont kernel cokernel factor ∧ UnaryHistory factor := by
  intro carrier
  have homUnary : UnaryHistory hom := carrier.right.left
  have zeroUnary : UnaryHistory zero :=
    unary_transport unary_empty (hsame_symm carrier.right.right.right.left)
  have kernelUnary : UnaryHistory kernel :=
    unary_cont_closed homUnary zeroUnary carrier.right.right.right.right.right.right.left
  have cokernelUnary : UnaryHistory cokernel :=
    unary_cont_closed zeroUnary homUnary carrier.right.right.right.right.right.right.right.left
  have factorUnary : UnaryHistory factor :=
    unary_cont_closed kernelUnary cokernelUnary carrier.right.right.right.right.right.right.right.right
  exact And.intro carrier.right.right.left
    (And.intro carrier.right.right.right.right.right.right.left
      (And.intro carrier.right.right.right.right.right.right.right.left
        (And.intro carrier.right.right.right.right.right.right.right.right factorUnary)))

end BEDC.Derived.AbelianCatUp
