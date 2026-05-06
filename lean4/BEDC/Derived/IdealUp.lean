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

theorem RingMapIdealPreimage_closure_rows
    {CarrierS CarrierT J : BHist -> Prop}
    {ClassifierS ClassifierT : BHist -> BHist -> Prop}
    {zeroS zeroT : BHist}
    {addS mulS addT mulT : BHist -> BHist -> BHist}
    {negS negT f : BHist -> BHist}
    (sourceCert : NameCert CarrierS ClassifierS)
    (targetCert : NameCert CarrierT ClassifierT)
    (sourceZero : CarrierS zeroS)
    (sourceAdd : forall {x y : BHist}, CarrierS x -> CarrierS y -> CarrierS (addS x y))
    (sourceNeg : forall {x : BHist}, CarrierS x -> CarrierS (negS x))
    (sourceMul : forall {x y : BHist}, CarrierS x -> CarrierS y -> CarrierS (mulS x y))
    (mapCarrier : forall {x : BHist}, CarrierS x -> CarrierT (f x))
    (mapClassifier :
      forall {x y : BHist}, CarrierS x -> CarrierS y -> ClassifierS x y ->
        ClassifierT (f x) (f y))
    (mapZero : ClassifierT (f zeroS) zeroT)
    (mapAdd :
      forall {x y : BHist}, CarrierS x -> CarrierS y ->
        ClassifierT (f (addS x y)) (addT (f x) (f y)))
    (mapNeg :
      forall {x : BHist}, CarrierS x -> ClassifierT (f (negS x)) (negT (f x)))
    (mapMul :
      forall {x y : BHist}, CarrierS x -> CarrierS y ->
        ClassifierT (f (mulS x y)) (mulT (f x) (f y)))
    (idealSupport : forall {x : BHist}, J x -> CarrierT x)
    (idealZero : J zeroT)
    (idealAdd : forall {x y : BHist}, J x -> J y -> J (addT x y))
    (idealNeg : forall {x : BHist}, J x -> J (negT x))
    (idealMul : forall {x y : BHist}, J x -> J y -> J (mulT x y))
    (idealTransport : forall {x y : BHist}, J x -> ClassifierT x y -> J y)
    (idealAbsorb :
      forall {r x : BHist}, CarrierT r -> J x -> J (mulT r x) ∧ J (mulT x r)) :
    (let Preimage : BHist -> Prop := fun x => CarrierS x ∧ J (f x);
      (forall {x : BHist}, Preimage x -> CarrierS x) ∧
        Preimage zeroS ∧
        (forall {x y : BHist}, Preimage x -> Preimage y -> Preimage (addS x y)) ∧
        (forall {x : BHist}, Preimage x -> Preimage (negS x)) ∧
        (forall {x y : BHist}, Preimage x -> Preimage y -> Preimage (mulS x y)) ∧
        (forall {x y : BHist}, Preimage x -> ClassifierS x y -> Preimage y) ∧
        (forall {r x : BHist}, CarrierS r -> Preimage x ->
          Preimage (mulS r x) ∧ Preimage (mulS x r))) := by
  dsimp
  constructor
  · intro x preimageX
    exact preimageX.left
  · constructor
    · constructor
      · exact sourceZero
      · have sameTargetZero : ClassifierT zeroT (f zeroS) :=
          NameCert.equiv_symm targetCert mapZero
        exact idealTransport idealZero sameTargetZero
    · constructor
      · intro x y preimageX preimageY
        constructor
        · exact sourceAdd preimageX.left preimageY.left
        · have mappedSum : J (addT (f x) (f y)) :=
            idealAdd preimageX.right preimageY.right
          have sameSum : ClassifierT (addT (f x) (f y)) (f (addS x y)) :=
            NameCert.equiv_symm targetCert (mapAdd preimageX.left preimageY.left)
          exact idealTransport mappedSum sameSum
      · constructor
        · intro x preimageX
          constructor
          · exact sourceNeg preimageX.left
          · have mappedNeg : J (negT (f x)) := idealNeg preimageX.right
            have sameNeg : ClassifierT (negT (f x)) (f (negS x)) :=
              NameCert.equiv_symm targetCert (mapNeg preimageX.left)
            exact idealTransport mappedNeg sameNeg
        · constructor
          · intro x y preimageX preimageY
            constructor
            · exact sourceMul preimageX.left preimageY.left
            · have mappedProduct : J (mulT (f x) (f y)) :=
                idealMul preimageX.right preimageY.right
              have sameProduct : ClassifierT (mulT (f x) (f y)) (f (mulS x y)) :=
                NameCert.equiv_symm targetCert (mapMul preimageX.left preimageY.left)
              exact idealTransport mappedProduct sameProduct
          · constructor
            · intro x y preimageX sameXY
              have carrierY : CarrierS y :=
                NameCert.carrier_respects_equiv sourceCert sameXY preimageX.left
              have sameImage : ClassifierT (f x) (f y) :=
                mapClassifier preimageX.left carrierY sameXY
              exact And.intro carrierY (idealTransport preimageX.right sameImage)
            · intro r x carrierR preimageX
              have carrierFX : CarrierT (f x) := idealSupport preimageX.right
              have carrierFR : CarrierT (f r) := mapCarrier carrierR
              have targetAbsorb : J (mulT (f r) (f x)) ∧ J (mulT (f x) (f r)) :=
                idealAbsorb carrierFR preimageX.right
              constructor
              · constructor
                · exact sourceMul carrierR preimageX.left
                · have sameLeft : ClassifierT (mulT (f r) (f x)) (f (mulS r x)) :=
                    NameCert.equiv_symm targetCert (mapMul carrierR preimageX.left)
                  exact idealTransport targetAbsorb.left sameLeft
              · constructor
                · exact sourceMul preimageX.left carrierR
                · have targetRight : J (mulT (f x) (f r)) := targetAbsorb.right
                  have sameRight : ClassifierT (mulT (f x) (f r)) (f (mulS x r)) :=
                    NameCert.equiv_symm targetCert (mapMul preimageX.left carrierR)
                  exact idealTransport targetRight sameRight

end BEDC.Derived.IdealUp
