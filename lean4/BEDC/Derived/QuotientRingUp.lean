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

end BEDC.Derived.QuotientRingUp
