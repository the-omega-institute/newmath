import BEDC.FKernel.NameCert

namespace BEDC.Derived.QuotientRingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def QuotientRingIdealCoset (Carrier I : BHist -> Prop) (sub : BHist -> BHist -> BHist)
    (a b : BHist) : Prop :=
  Carrier a ∧ Carrier b ∧ I (sub a b)

theorem QuotientRingIdealCoset_zero_classification
    {Carrier I : BHist -> Prop}
    {Classifier : BHist -> BHist -> Prop}
    {sub : BHist -> BHist -> BHist}
    {zero a : BHist}
    (cert : NameCert Carrier Classifier)
    (carrierZero : Carrier zero)
    (idealTransport : forall {x y : BHist}, I x -> Classifier x y -> I y)
    (subZeroClassified : Carrier a -> Classifier (sub a zero) a) :
    QuotientRingIdealCoset Carrier I sub a zero <-> Carrier a ∧ I a := by
  constructor
  · intro cosetZero
    have carrierA : Carrier a := cosetZero.left
    have idealSub : I (sub a zero) := cosetZero.right.right
    have sameSubA : Classifier (sub a zero) a := subZeroClassified carrierA
    exact And.intro carrierA (idealTransport idealSub sameSubA)
  · intro carrierAndIdeal
    have sameSubA : Classifier (sub a zero) a := subZeroClassified carrierAndIdeal.left
    have sameASub : Classifier a (sub a zero) := NameCert.equiv_symm cert sameSubA
    exact And.intro carrierAndIdeal.left
      (And.intro carrierZero (idealTransport carrierAndIdeal.right sameASub))

theorem QuotientRingIdealCoset_multiplication_descent
    {Carrier I : BHist -> Prop}
    {Classifier : BHist -> BHist -> Prop}
    {sub add mul : BHist -> BHist -> BHist}
    {a a' b b' : BHist}
    (cert : NameCert Carrier Classifier)
    (carrierMul : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (mul x y))
    (idealAdd : forall {x y : BHist}, I x -> I y -> I (add x y))
    (idealTransport : forall {x y : BHist}, I x -> Classifier x y -> I y)
    (idealAbsorb :
      forall {r x : BHist}, Carrier r -> I x -> I (mul r x) ∧ I (mul x r))
    (productDiffClassified :
      Classifier (sub (mul a b) (mul a' b'))
        (add (mul (sub a a') b) (mul a' (sub b b')))) :
    QuotientRingIdealCoset Carrier I sub a a' ->
      QuotientRingIdealCoset Carrier I sub b b' ->
        QuotientRingIdealCoset Carrier I sub (mul a b) (mul a' b') := by
  intro cosetA cosetB
  have carrierProductLeft : Carrier (mul a b) :=
    carrierMul cosetA.left cosetB.left
  have carrierProductRight : Carrier (mul a' b') :=
    carrierMul cosetA.right.left cosetB.right.left
  have idealLeftProduct : I (mul (sub a a') b) :=
    (idealAbsorb cosetB.left cosetA.right.right).right
  have idealRightProduct : I (mul a' (sub b b')) :=
    (idealAbsorb cosetA.right.left cosetB.right.right).left
  have idealProductSum : I (add (mul (sub a a') b) (mul a' (sub b b'))) :=
    idealAdd idealLeftProduct idealRightProduct
  have productSumClassified :
      Classifier (add (mul (sub a a') b) (mul a' (sub b b')))
        (sub (mul a b) (mul a' b')) :=
    NameCert.equiv_symm cert productDiffClassified
  exact And.intro carrierProductLeft
    (And.intro carrierProductRight (idealTransport idealProductSum productSumClassified))

end BEDC.Derived.QuotientRingUp
