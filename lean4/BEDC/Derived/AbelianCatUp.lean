import BEDC.Derived.CategoryUp
import BEDC.Derived.GroupUp

namespace BEDC.Derived.AbelianCatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp
open BEDC.Derived.GroupUp

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

end BEDC.Derived.AbelianCatUp
