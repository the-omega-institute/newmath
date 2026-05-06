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

theorem QuotientRingIdealCoset_mul_descends
    {Carrier I : BHist -> Prop} {Classifier : BHist -> BHist -> Prop}
    {add mul sub : BHist -> BHist -> BHist}
    (cert : NameCert Carrier Classifier)
    (mulCarrier : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (mul x y))
    (I_add : forall {x y : BHist}, I x -> I y -> I (add x y))
    (I_transport : forall {x y : BHist}, I x -> Classifier x y -> I y)
    (I_leftAbsorb : forall {r x : BHist}, Carrier r -> I x -> I (mul r x))
    (I_rightAbsorb : forall {r x : BHist}, Carrier r -> I x -> I (mul x r))
    (productDifference : forall {a a' b b' : BHist},
      Classifier (add (mul (sub a a') b) (mul a' (sub b b')))
        (sub (mul a b) (mul a' b'))) {a a' b b' : BHist} :
    QuotientRingIdealCoset Carrier I sub a a' ->
      QuotientRingIdealCoset Carrier I sub b b' ->
        QuotientRingIdealCoset Carrier I sub (mul a b) (mul a' b') := by
  intro cosetA cosetB
  have _certWitness : exists h : BHist, Carrier h := NameCert.carrier_inhabited cert
  have carrierA : Carrier a := cosetA.left
  have carrierA' : Carrier a' := cosetA.right.left
  have carrierB : Carrier b := cosetB.left
  have carrierB' : Carrier b' := cosetB.right.left
  have idealLeft : I (mul (sub a a') b) :=
    I_rightAbsorb carrierB cosetA.right.right
  have idealRight : I (mul a' (sub b b')) :=
    I_leftAbsorb carrierA' cosetB.right.right
  have idealSum : I (add (mul (sub a a') b) (mul a' (sub b b'))) :=
    I_add idealLeft idealRight
  have idealProductDifference : I (sub (mul a b) (mul a' b')) :=
    I_transport idealSum productDifference
  exact And.intro (mulCarrier carrierA carrierB)
    (And.intro (mulCarrier carrierA' carrierB') idealProductDifference)

end BEDC.Derived.QuotientRingUp
