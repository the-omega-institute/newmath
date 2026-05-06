import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert

namespace BEDC.Derived.IdealUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem IdealIntersection_closure_rows
    {Carrier I J : BHist -> Prop}
    {Classifier : BHist -> BHist -> Prop}
    {zero : BHist}
    {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist}
    (cert : NameCert Carrier Classifier)
    (carrierZero : Carrier zero)
    (carrierAdd : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (add x y))
    (carrierNeg : forall {x : BHist}, Carrier x -> Carrier (neg x))
    (carrierMul : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (mul x y))
    (I_support : forall {x : BHist}, I x -> Carrier x)
    (I_zero : I zero)
    (I_add : forall {x y : BHist}, I x -> I y -> I (add x y))
    (I_neg : forall {x : BHist}, I x -> I (neg x))
    (I_mul : forall {x y : BHist}, I x -> I y -> I (mul x y))
    (I_transport : forall {x y : BHist}, I x -> Classifier x y -> I y)
    (I_absorb : forall {r x : BHist}, Carrier r -> I x -> I (mul r x) ∧ I (mul x r))
    (J_support : forall {x : BHist}, J x -> Carrier x)
    (J_zero : J zero)
    (J_add : forall {x y : BHist}, J x -> J y -> J (add x y))
    (J_neg : forall {x : BHist}, J x -> J (neg x))
    (J_mul : forall {x y : BHist}, J x -> J y -> J (mul x y))
    (J_transport : forall {x y : BHist}, J x -> Classifier x y -> J y)
    (J_absorb : forall {r x : BHist}, Carrier r -> J x -> J (mul r x) ∧ J (mul x r)) :
    (forall {x : BHist}, I x ∧ J x -> Carrier x) ∧
      (I zero ∧ J zero) ∧
      (forall {x y : BHist}, I x ∧ J x -> I y ∧ J y -> I (add x y) ∧ J (add x y)) ∧
      (forall {x : BHist}, I x ∧ J x -> I (neg x) ∧ J (neg x)) ∧
      (forall {x y : BHist}, I x ∧ J x -> I y ∧ J y -> I (mul x y) ∧ J (mul x y)) ∧
      (forall {x y : BHist}, I x ∧ J x -> Classifier x y -> I y ∧ J y) ∧
      (forall {r x : BHist}, Carrier r -> I x ∧ J x ->
        (I (mul r x) ∧ J (mul r x)) ∧ (I (mul x r) ∧ J (mul x r))) := by
  constructor
  · intro x intersection
    have carrierX : Carrier x := I_support intersection.left
    exact NameCert.carrier_respects_equiv cert (NameCert.equiv_refl cert carrierX) carrierX
  · constructor
    · exact And.intro I_zero J_zero
    · constructor
      · intro x y left right
        exact And.intro (I_add left.left right.left) (J_add left.right right.right)
      · constructor
        · intro x intersection
          exact And.intro (I_neg intersection.left) (J_neg intersection.right)
        · constructor
          · intro x y left right
            exact And.intro (I_mul left.left right.left) (J_mul left.right right.right)
          · constructor
            · intro x y intersection classified
              exact And.intro (I_transport intersection.left classified)
                (J_transport intersection.right classified)
            · intro r x carrierR intersection
              have iAbsorb : I (mul r x) ∧ I (mul x r) :=
                I_absorb carrierR intersection.left
              have jAbsorb : J (mul r x) ∧ J (mul x r) :=
                J_absorb carrierR intersection.right
              exact And.intro (And.intro iAbsorb.left jAbsorb.left)
                (And.intro iAbsorb.right jAbsorb.right)

def FiniteIdealMeet
    (Carrier : BHist -> Prop) (indices : ProbeBundle BHist)
    (Family : BHist -> BHist -> Prop) (x : BHist) : Prop :=
  Carrier x ∧ forall i : BHist, InBundle i indices -> Family i x

theorem FiniteIdealMeet_closure_rows
    {Carrier : BHist -> Prop} {indices : ProbeBundle BHist}
    {Classifier : BHist -> BHist -> Prop}
    {zero : BHist}
    {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist}
    {Family : BHist -> BHist -> Prop}
    (carrierZero : Carrier zero)
    (carrierAdd : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (add x y))
    (carrierNeg : forall {x : BHist}, Carrier x -> Carrier (neg x))
    (carrierMul : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (mul x y))
    (carrierTransport : forall {x y : BHist}, Carrier x -> Classifier x y -> Carrier y)
    (familyZero : forall {i : BHist}, InBundle i indices -> Family i zero)
    (familyAdd :
      forall {i x y : BHist},
        InBundle i indices -> Family i x -> Family i y -> Family i (add x y))
    (familyNeg :
      forall {i x : BHist}, InBundle i indices -> Family i x -> Family i (neg x))
    (familyMul :
      forall {i x y : BHist},
        InBundle i indices -> Family i x -> Family i y -> Family i (mul x y))
    (familyTransport :
      forall {i x y : BHist},
        InBundle i indices -> Family i x -> Classifier x y -> Family i y)
    (familyAbsorb :
      forall {i r x : BHist},
        InBundle i indices -> Carrier r -> Family i x ->
          Family i (mul r x) ∧ Family i (mul x r)) :
    (forall {x : BHist}, FiniteIdealMeet Carrier indices Family x -> Carrier x) ∧
      FiniteIdealMeet Carrier indices Family zero ∧
      (forall {x y : BHist},
        FiniteIdealMeet Carrier indices Family x ->
          FiniteIdealMeet Carrier indices Family y ->
            FiniteIdealMeet Carrier indices Family (add x y)) ∧
      (forall {x : BHist},
        FiniteIdealMeet Carrier indices Family x ->
          FiniteIdealMeet Carrier indices Family (neg x)) ∧
      (forall {x y : BHist},
        FiniteIdealMeet Carrier indices Family x ->
          FiniteIdealMeet Carrier indices Family y ->
            FiniteIdealMeet Carrier indices Family (mul x y)) ∧
      (forall {x y : BHist},
        FiniteIdealMeet Carrier indices Family x ->
          Classifier x y -> FiniteIdealMeet Carrier indices Family y) ∧
      (forall {r x : BHist},
        Carrier r -> FiniteIdealMeet Carrier indices Family x ->
          FiniteIdealMeet Carrier indices Family (mul r x) ∧
            FiniteIdealMeet Carrier indices Family (mul x r)) := by
  constructor
  · intro x meetX
    exact meetX.left
  · constructor
    · constructor
      · exact carrierZero
      · intro i memberI
        exact familyZero memberI
    · constructor
      · intro x y meetX meetY
        constructor
        · exact carrierAdd meetX.left meetY.left
        · intro i memberI
          exact familyAdd memberI (meetX.right i memberI) (meetY.right i memberI)
      · constructor
        · intro x meetX
          constructor
          · exact carrierNeg meetX.left
          · intro i memberI
            exact familyNeg memberI (meetX.right i memberI)
        · constructor
          · intro x y meetX meetY
            constructor
            · exact carrierMul meetX.left meetY.left
            · intro i memberI
              exact familyMul memberI (meetX.right i memberI) (meetY.right i memberI)
          · constructor
            · intro x y meetX classified
              constructor
              · exact carrierTransport meetX.left classified
              · intro i memberI
                exact familyTransport memberI (meetX.right i memberI) classified
            · intro r x carrierR meetX
              constructor
              · constructor
                · exact carrierMul carrierR meetX.left
                · intro i memberI
                  exact (familyAbsorb memberI carrierR (meetX.right i memberI)).left
              · constructor
                · exact carrierMul meetX.left carrierR
                · intro i memberI
                  exact (familyAbsorb memberI carrierR (meetX.right i memberI)).right

theorem IdealZeroPredicate_closure_rows
    {Carrier : BHist -> Prop}
    {Classifier : BHist -> BHist -> Prop}
    {zero : BHist}
    {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist}
    (cert : NameCert Carrier Classifier)
    (zeroCarrier : Carrier zero)
    (addCarrier : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (add x y))
    (negCarrier : forall {x : BHist}, Carrier x -> Carrier (neg x))
    (mulCarrier : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (mul x y))
    (addCongr :
      forall {x x' y y' : BHist}, Carrier x -> Carrier x' -> Carrier y -> Carrier y' ->
        Classifier x x' -> Classifier y y' -> Classifier (add x y) (add x' y'))
    (negCongr :
      forall {x y : BHist}, Carrier x -> Carrier y -> Classifier x y ->
        Classifier (neg x) (neg y))
    (mulCongr :
      forall {x x' y y' : BHist}, Carrier x -> Carrier x' -> Carrier y -> Carrier y' ->
        Classifier x x' -> Classifier y y' -> Classifier (mul x y) (mul x' y'))
    (addZeroZero : Classifier (add zero zero) zero)
    (negZero : Classifier (neg zero) zero)
    (mulZeroZero : Classifier (mul zero zero) zero)
    (mulLeftZero : forall {r : BHist}, Carrier r -> Classifier (mul zero r) zero)
    (mulRightZero : forall {r : BHist}, Carrier r -> Classifier (mul r zero) zero) :
    (forall {x : BHist}, Carrier x ∧ Classifier x zero -> Carrier x) ∧
      (Carrier zero ∧ Classifier zero zero) ∧
      (forall {x y : BHist}, Carrier x ∧ Classifier x zero ->
        Carrier y ∧ Classifier y zero -> Carrier (add x y) ∧ Classifier (add x y) zero) ∧
      (forall {x : BHist}, Carrier x ∧ Classifier x zero ->
        Carrier (neg x) ∧ Classifier (neg x) zero) ∧
      (forall {x y : BHist}, Carrier x ∧ Classifier x zero ->
        Carrier y ∧ Classifier y zero -> Carrier (mul x y) ∧ Classifier (mul x y) zero) ∧
      (forall {x y : BHist}, Carrier x ∧ Classifier x zero -> Classifier x y ->
        Carrier y ∧ Classifier y zero) ∧
      (forall {r x : BHist}, Carrier r -> Carrier x ∧ Classifier x zero ->
        (Carrier (mul r x) ∧ Classifier (mul r x) zero) ∧
          (Carrier (mul x r) ∧ Classifier (mul x r) zero)) := by
  have zeroRefl : Classifier zero zero := NameCert.equiv_refl cert zeroCarrier
  constructor
  · intro x membership
    exact membership.left
  · constructor
    · exact And.intro zeroCarrier zeroRefl
    · constructor
      · intro x y memberX memberY
        have addCarrierXY : Carrier (add x y) := addCarrier memberX.left memberY.left
        have addZeroCarrier : Carrier (add zero zero) := addCarrier zeroCarrier zeroCarrier
        have addClassified : Classifier (add x y) (add zero zero) :=
          addCongr memberX.left zeroCarrier memberY.left zeroCarrier memberX.right memberY.right
        have addToZero : Classifier (add x y) zero :=
          NameCert.equiv_trans cert addClassified addZeroZero
        exact And.intro addCarrierXY addToZero
      · constructor
        · intro x memberX
          have negCarrierX : Carrier (neg x) := negCarrier memberX.left
          have negClassified : Classifier (neg x) (neg zero) :=
            negCongr memberX.left zeroCarrier memberX.right
          have negToZero : Classifier (neg x) zero :=
            NameCert.equiv_trans cert negClassified negZero
          exact And.intro negCarrierX negToZero
        · constructor
          · intro x y memberX memberY
            have mulCarrierXY : Carrier (mul x y) := mulCarrier memberX.left memberY.left
            have mulZeroCarrier : Carrier (mul zero zero) := mulCarrier zeroCarrier zeroCarrier
            have mulClassified : Classifier (mul x y) (mul zero zero) :=
              mulCongr memberX.left zeroCarrier memberY.left zeroCarrier
                memberX.right memberY.right
            have mulToZero : Classifier (mul x y) zero :=
              NameCert.equiv_trans cert mulClassified mulZeroZero
            exact And.intro mulCarrierXY mulToZero
          · constructor
            · intro x y memberX classifiedXY
              have carrierY : Carrier y :=
                NameCert.carrier_respects_equiv cert classifiedXY memberX.left
              have classifiedYX : Classifier y x := NameCert.equiv_symm cert classifiedXY
              have yToZero : Classifier y zero :=
                NameCert.equiv_trans cert classifiedYX memberX.right
              exact And.intro carrierY yToZero
            · intro r x carrierR memberX
              have leftCarrier : Carrier (mul r x) := mulCarrier carrierR memberX.left
              have rightCarrier : Carrier (mul x r) := mulCarrier memberX.left carrierR
              have leftCongr : Classifier (mul r x) (mul r zero) :=
                mulCongr carrierR carrierR memberX.left zeroCarrier
                  (NameCert.equiv_refl cert carrierR) memberX.right
              have leftZero : Classifier (mul r x) zero :=
                NameCert.equiv_trans cert leftCongr (mulRightZero carrierR)
              have rightCongr : Classifier (mul x r) (mul zero r) :=
                mulCongr memberX.left zeroCarrier carrierR carrierR
                  memberX.right (NameCert.equiv_refl cert carrierR)
              have rightZero : Classifier (mul x r) zero :=
                NameCert.equiv_trans cert rightCongr (mulLeftZero carrierR)
              exact And.intro (And.intro leftCarrier leftZero) (And.intro rightCarrier rightZero)

end BEDC.Derived.IdealUp
