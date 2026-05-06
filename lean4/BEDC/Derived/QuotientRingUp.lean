import BEDC.FKernel.NameCert

namespace BEDC.Derived.QuotientRingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem QuotientRingIdealCosetRelation_equivalence_rows
    {Carrier Ideal : BHist -> Prop}
    {Classifier : BHist -> BHist -> Prop}
    {zero : BHist}
    {add sub neg : BHist -> BHist -> BHist}
    (cert : NameCert Carrier Classifier)
    (idealZero : Ideal zero)
    (idealNeg : forall {x : BHist}, Ideal x -> Ideal (neg x zero))
    (idealAdd : forall {x y : BHist}, Ideal x -> Ideal y -> Ideal (add x y))
    (idealTransport : forall {x y : BHist}, Ideal x -> Classifier x y -> Ideal y)
    (subSelf : forall {a : BHist}, Carrier a -> Classifier (sub a a) zero)
    (subSymm :
      forall {a b : BHist}, Carrier a -> Carrier b ->
        Classifier (neg (sub a b) zero) (sub b a))
    (subTrans :
      forall {a b c : BHist}, Carrier a -> Carrier b -> Carrier c ->
        Classifier (add (sub a b) (sub b c)) (sub a c)) :
    (forall {a : BHist}, Carrier a -> Carrier a ∧ Carrier a ∧ Ideal (sub a a)) ∧
      (forall {a b : BHist}, Carrier a ∧ Carrier b ∧ Ideal (sub a b) ->
        Carrier b ∧ Carrier a ∧ Ideal (sub b a)) ∧
      (forall {a b c : BHist}, Carrier a ∧ Carrier b ∧ Ideal (sub a b) ->
        Carrier b ∧ Carrier c ∧ Ideal (sub b c) ->
          Carrier a ∧ Carrier c ∧ Ideal (sub a c)) := by
  constructor
  · intro a carrierA
    have carrierAFromCert : Carrier a :=
      NameCert.carrier_respects_equiv cert (NameCert.equiv_refl cert carrierA) carrierA
    have selfToZero : Classifier (sub a a) zero := subSelf carrierAFromCert
    have zeroToSelf : Classifier zero (sub a a) := NameCert.equiv_symm cert selfToZero
    exact And.intro carrierAFromCert
      (And.intro carrierAFromCert (idealTransport idealZero zeroToSelf))
  · constructor
    · intro a b cosetAB
      have carrierA : Carrier a := cosetAB.left
      have carrierB : Carrier b := cosetAB.right.left
      have negIdeal : Ideal (neg (sub a b) zero) := idealNeg cosetAB.right.right
      have negToReverse : Classifier (neg (sub a b) zero) (sub b a) :=
        subSymm carrierA carrierB
      exact And.intro carrierB (And.intro carrierA (idealTransport negIdeal negToReverse))
    · intro a b c cosetAB cosetBC
      have carrierA : Carrier a := cosetAB.left
      have carrierB : Carrier b := cosetAB.right.left
      have carrierC : Carrier c := cosetBC.right.left
      have addedIdeal : Ideal (add (sub a b) (sub b c)) :=
        idealAdd cosetAB.right.right cosetBC.right.right
      have addedToAC : Classifier (add (sub a b) (sub b c)) (sub a c) :=
        subTrans carrierA carrierB carrierC
      exact And.intro carrierA (And.intro carrierC (idealTransport addedIdeal addedToAC))

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

theorem QuotientRingIdealCoset_multiplication_descends
    {Carrier Ideal : BHist -> Prop}
    {Classifier : BHist -> BHist -> Prop}
    {mul sub add : BHist -> BHist -> BHist}
    {a aPrime b bPrime : BHist}
    (cert : NameCert Carrier Classifier)
    (mulCarrier : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (mul x y))
    (idealAdd : forall {x y : BHist}, Ideal x -> Ideal y -> Ideal (add x y))
    (idealTransport : forall {x y : BHist}, Ideal x -> Classifier x y -> Ideal y)
    (idealAbsorb :
      forall {r x : BHist}, Carrier r -> Ideal x -> Ideal (mul r x) ∧ Ideal (mul x r))
    (productDifference :
      Classifier (add (mul (sub a aPrime) b) (mul aPrime (sub b bPrime)))
        (sub (mul a b) (mul aPrime bPrime))) :
    QuotientRingIdealCoset Carrier Ideal sub a aPrime ->
      QuotientRingIdealCoset Carrier Ideal sub b bPrime ->
        QuotientRingIdealCoset Carrier Ideal sub (mul a b) (mul aPrime bPrime) := by
  intro cosetA cosetB
  have carrierA : Carrier a := cosetA.left
  have carrierAPrime : Carrier aPrime := cosetA.right.left
  have carrierB : Carrier b := cosetB.left
  have carrierBPrime : Carrier bPrime := cosetB.right.left
  have carrierAFromCert : Carrier a :=
    NameCert.carrier_respects_equiv cert (NameCert.equiv_refl cert carrierA) carrierA
  have carrierAPrimeFromCert : Carrier aPrime :=
    NameCert.carrier_respects_equiv cert (NameCert.equiv_refl cert carrierAPrime) carrierAPrime
  have carrierBFromCert : Carrier b :=
    NameCert.carrier_respects_equiv cert (NameCert.equiv_refl cert carrierB) carrierB
  have carrierBPrimeFromCert : Carrier bPrime :=
    NameCert.carrier_respects_equiv cert (NameCert.equiv_refl cert carrierBPrime) carrierBPrime
  have idealA : Ideal (sub a aPrime) := cosetA.right.right
  have idealB : Ideal (sub b bPrime) := cosetB.right.right
  have firstAbsorbed : Ideal (mul (sub a aPrime) b) :=
    (idealAbsorb carrierBFromCert idealA).right
  have secondAbsorbed : Ideal (mul aPrime (sub b bPrime)) :=
    (idealAbsorb carrierAPrimeFromCert idealB).left
  have combinedIdeal :
      Ideal (add (mul (sub a aPrime) b) (mul aPrime (sub b bPrime))) :=
    idealAdd firstAbsorbed secondAbsorbed
  have productIdeal : Ideal (sub (mul a b) (mul aPrime bPrime)) :=
    idealTransport combinedIdeal productDifference
  exact And.intro (mulCarrier carrierAFromCert carrierBFromCert)
    (And.intro (mulCarrier carrierAPrimeFromCert carrierBPrimeFromCert) productIdeal)

end BEDC.Derived.QuotientRingUp
