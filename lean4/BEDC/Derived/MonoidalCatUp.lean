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

theorem MonoidalCatSingleton_associator_unitors {x y z left right leftUnit rightUnit :
    BHist} :
    UnaryHistory x ->
      UnaryHistory y ->
        UnaryHistory z ->
          Cont (append x y) z left ->
            Cont x (append y z) right ->
              Cont BHist.Empty x leftUnit ->
                Cont x BHist.Empty rightUnit ->
                  CategoryHomCarrier (append (append x y) z) (append x (append y z))
                      BHist.Empty ∧
                    CategoryHomCarrier (append BHist.Empty x) x BHist.Empty ∧
                      CategoryHomCarrier (append x BHist.Empty) x BHist.Empty ∧
                        hsame left right ∧ hsame leftUnit x ∧ hsame rightUnit x := by
  intro xUnary yUnary zUnary leftCont rightCont leftUnitCont rightUnitCont
  have assocSourceUnary : UnaryHistory (append (append x y) z) :=
    unary_append_closed (unary_append_closed xUnary yUnary) zUnary
  have assocTargetUnary : UnaryHistory (append x (append y z)) :=
    unary_append_closed xUnary (unary_append_closed yUnary zUnary)
  have assocSame : hsame (append (append x y) z) (append x (append y z)) :=
    append_assoc x y z
  have assocHom :
      CategoryHomCarrier (append (append x y) z) (append x (append y z)) BHist.Empty :=
    CategoryHomCarrier_empty_identity_iff.mpr
      (And.intro assocSourceUnary (And.intro assocTargetUnary assocSame))
  have leftUnitSourceUnary : UnaryHistory (append BHist.Empty x) :=
    unary_append_closed unary_empty xUnary
  have leftUnitSame : hsame (append BHist.Empty x) x :=
    append_empty_left x
  have leftUnitHom : CategoryHomCarrier (append BHist.Empty x) x BHist.Empty :=
    CategoryHomCarrier_empty_identity_iff.mpr
      (And.intro leftUnitSourceUnary (And.intro xUnary leftUnitSame))
  have rightUnitSourceUnary : UnaryHistory (append x BHist.Empty) :=
    unary_append_closed xUnary unary_empty
  have rightUnitSame : hsame (append x BHist.Empty) x :=
    append_empty_right x
  have rightUnitHom : CategoryHomCarrier (append x BHist.Empty) x BHist.Empty :=
    CategoryHomCarrier_empty_identity_iff.mpr
      (And.intro rightUnitSourceUnary (And.intro xUnary rightUnitSame))
  exact And.intro assocHom
    (And.intro leftUnitHom
      (And.intro rightUnitHom
        (And.intro
          (cont_assoc_hsame (cont_intro rfl) leftCont (cont_intro rfl) rightCont)
          (And.intro (cont_left_unit_result leftUnitCont)
            (cont_deterministic rightUnitCont (cont_right_unit x))))))

end BEDC.Derived.MonoidalCatUp
