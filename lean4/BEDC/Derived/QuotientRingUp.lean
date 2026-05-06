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

end BEDC.Derived.QuotientRingUp
