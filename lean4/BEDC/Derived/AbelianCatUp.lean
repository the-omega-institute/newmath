import BEDC.Derived.CategoryUp
import BEDC.Derived.GroupUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.AbelianCatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
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

theorem AbelianCatKernelCokernelCarrier_zero_biproduct_readback
    {obj hom zero biprod add kernel cokernel factor : BHist} :
    AbelianCatKernelCokernelCarrier obj hom zero biprod add kernel cokernel factor ->
      GroupSingletonCarrier zero ∧ Cont BHist.Empty hom biprod ∧ Cont hom BHist.Empty add ∧
        hsame biprod hom ∧ hsame add hom ∧ UnaryHistory biprod ∧ UnaryHistory add := by
  intro carrier
  have homUnary : UnaryHistory hom := carrier.right.left
  have zeroCarrier : GroupSingletonCarrier zero := carrier.right.right.right.left
  have biprodRow : Cont BHist.Empty hom biprod := carrier.right.right.right.right.left
  have addRow : Cont hom BHist.Empty add := carrier.right.right.right.right.right.left
  have biprodHom : hsame biprod hom := cont_left_unit_result biprodRow
  have addHom : hsame add hom := cont_right_unit_result addRow
  have biprodUnary : UnaryHistory biprod := unary_transport homUnary (hsame_symm biprodHom)
  have addUnary : UnaryHistory add := unary_transport homUnary (hsame_symm addHom)
  exact And.intro zeroCarrier
    (And.intro biprodRow
      (And.intro addRow
        (And.intro biprodHom (And.intro addHom (And.intro biprodUnary addUnary)))))

def AbelianCatAdditiveCarrier
    (source target zero add kernel cokernel factor : BHist) : Prop :=
  CategoryHomCarrier source target zero ∧ GroupSingletonCarrier add ∧ UnaryHistory kernel ∧
    UnaryHistory cokernel ∧ UnaryHistory factor ∧ Cont zero add kernel ∧
      Cont kernel cokernel factor

def AbelianCatAdditiveClassifier
    (source target zero add kernel cokernel factor source' target' zero' add' kernel' cokernel'
      factor' : BHist) : Prop :=
  hsame source source' ∧ hsame target target' ∧ hsame zero zero' ∧ hsame add add' ∧
    hsame kernel kernel' ∧ hsame cokernel cokernel' ∧ hsame factor factor'

theorem AbelianCatAdditiveCarrier_classifier_transport
    {source target zero add kernel cokernel factor source' target' zero' add' kernel' cokernel'
      factor' : BHist} :
    AbelianCatAdditiveCarrier source target zero add kernel cokernel factor ->
      AbelianCatAdditiveClassifier source target zero add kernel cokernel factor source' target'
        zero' add' kernel' cokernel' factor' ->
        AbelianCatAdditiveCarrier source' target' zero' add' kernel' cokernel' factor' ∧
          CategoryHomCarrier source' target' zero' ∧ GroupSingletonCarrier add' ∧
            Cont zero' add' kernel' ∧ Cont kernel' cokernel' factor' := by
  intro carrier classified
  have sourceSame : hsame source source' := classified.left
  have targetSame : hsame target target' := classified.right.left
  have zeroSame : hsame zero zero' := classified.right.right.left
  have homCarrier : CategoryHomCarrier source' target' zero' :=
    CategoryHomCarrier_hsame_transport sourceSame targetSame zeroSame carrier.left
  cases sourceSame
  cases targetSame
  cases zeroSame
  cases classified.right.right.right.left
  cases classified.right.right.right.right.left
  cases classified.right.right.right.right.right.left
  cases classified.right.right.right.right.right.right
  exact And.intro carrier
    (And.intro homCarrier
      (And.intro carrier.right.left
        (And.intro carrier.right.right.right.right.right.left
          carrier.right.right.right.right.right.right)))

theorem AbelianCatKernelCokernel_visible_factorization
    {f kerObj cokObj imageObj coimageObj comparison recomposed : BHist} :
    hsame f BHist.Empty -> Cont BHist.Empty f kerObj -> Cont f BHist.Empty cokObj ->
      Cont kerObj cokObj imageObj -> Cont imageObj BHist.Empty coimageObj ->
        Cont coimageObj BHist.Empty comparison -> Cont comparison BHist.Empty recomposed ->
          hsame kerObj BHist.Empty ∧ hsame cokObj BHist.Empty ∧
            hsame imageObj BHist.Empty ∧ hsame coimageObj BHist.Empty ∧
              hsame comparison BHist.Empty ∧ hsame recomposed f ∧ UnaryHistory kerObj ∧
                UnaryHistory cokObj ∧ UnaryHistory imageObj ∧ UnaryHistory coimageObj ∧
                  UnaryHistory comparison ∧ UnaryHistory recomposed := by
  intro fEmpty kerReadback cokReadback imageReadback coimageReadback comparisonReadback
    recomposedReadback
  have sameKerF : hsame kerObj f :=
    cont_left_unit_result kerReadback
  have kerEmpty : hsame kerObj BHist.Empty :=
    hsame_trans sameKerF fEmpty
  have sameCokF : hsame cokObj f :=
    cont_right_unit_result cokReadback
  have cokEmpty : hsame cokObj BHist.Empty :=
    hsame_trans sameCokF fEmpty
  have imageEmpty : hsame imageObj BHist.Empty :=
    cont_respects_hsame kerEmpty cokEmpty imageReadback (cont_left_unit BHist.Empty)
  have sameCoimageImage : hsame coimageObj imageObj :=
    cont_right_unit_result coimageReadback
  have coimageEmpty : hsame coimageObj BHist.Empty :=
    hsame_trans sameCoimageImage imageEmpty
  have sameComparisonCoimage : hsame comparison coimageObj :=
    cont_right_unit_result comparisonReadback
  have comparisonEmpty : hsame comparison BHist.Empty :=
    hsame_trans sameComparisonCoimage coimageEmpty
  have sameRecomposedComparison : hsame recomposed comparison :=
    cont_right_unit_result recomposedReadback
  have recomposedEmpty : hsame recomposed BHist.Empty :=
    hsame_trans sameRecomposedComparison comparisonEmpty
  have recomposedF : hsame recomposed f :=
    hsame_trans recomposedEmpty (hsame_symm fEmpty)
  have kerUnary : UnaryHistory kerObj :=
    unary_transport unary_empty (hsame_symm kerEmpty)
  have cokUnary : UnaryHistory cokObj :=
    unary_transport unary_empty (hsame_symm cokEmpty)
  have imageUnary : UnaryHistory imageObj :=
    unary_transport unary_empty (hsame_symm imageEmpty)
  have coimageUnary : UnaryHistory coimageObj :=
    unary_transport unary_empty (hsame_symm coimageEmpty)
  have comparisonUnary : UnaryHistory comparison :=
    unary_transport unary_empty (hsame_symm comparisonEmpty)
  have recomposedUnary : UnaryHistory recomposed :=
    unary_transport unary_empty (hsame_symm recomposedEmpty)
  exact And.intro kerEmpty
    (And.intro cokEmpty
      (And.intro imageEmpty
        (And.intro coimageEmpty
          (And.intro comparisonEmpty
            (And.intro recomposedF
              (And.intro kerUnary
                (And.intro cokUnary
                  (And.intro imageUnary
                  (And.intro coimageUnary
                      (And.intro comparisonUnary recomposedUnary))))))))))

end BEDC.Derived.AbelianCatUp
