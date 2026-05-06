import BEDC.Derived.CategoryUp
import BEDC.FKernel.Unary.Commutativity

namespace BEDC.Derived.MonoidalCatUp

open BEDC.Derived.CategoryUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def MonoidalCatSingletonTensor (h k : BHist) : BHist := append h k

theorem MonoidalCatSingleton_tensor_carrier {a b c d f g : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier c d g ->
      UnaryHistory (append a c) ∧
        CategoryHomCarrier (append a c) (append b d) (append f g) := by
  intro left right
  have sourceCarrier : UnaryHistory (append a c) :=
    unary_append_closed left.left right.left
  have targetCarrier : UnaryHistory (append b d) :=
    unary_append_closed left.right.left right.right.left
  have morphismCarrier : UnaryHistory (append f g) :=
    unary_append_closed left.right.right.left right.right.right.left
  have targetEq :
      append (append a c) (append f g) = append b d := by
    calc
      append (append a c) (append f g)
          = append a (append c (append f g)) :=
            append_assoc a c (append f g)
      _ = append a (append (append c f) g) :=
            congrArg (append a) (append_assoc c f g).symm
      _ = append a (append (append f c) g) :=
            congrArg (fun x => append a (append x g))
              (unary_append_comm right.left left.right.right.left)
      _ = append a (append f (append c g)) :=
            congrArg (append a) (append_assoc f c g)
      _ = append (append a f) (append c g) :=
            (append_assoc a f (append c g)).symm
      _ = append b (append c g) :=
            congrArg (fun x => append x (append c g)) left.right.right.right.symm
      _ = append b d :=
            congrArg (append b) right.right.right.right.symm
  exact And.intro sourceCarrier
    (And.intro sourceCarrier
      (And.intro targetCarrier
        (And.intro morphismCarrier (cont_intro targetEq.symm))))

end BEDC.Derived.MonoidalCatUp
