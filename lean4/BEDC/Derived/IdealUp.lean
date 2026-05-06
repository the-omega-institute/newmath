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

theorem IdealSum_closure_rows
    {Carrier I J : BHist -> Prop}
    {Classifier : BHist -> BHist -> Prop}
    {zero : BHist}
    {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist}
    (cert : NameCert Carrier Classifier)
    (carrierAdd : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (add x y))
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
    (J_absorb : forall {r x : BHist}, Carrier r -> J x -> J (mul r x) ∧ J (mul x r))
    (addCongr :
      forall {a a' b b' : BHist},
        Classifier a a' -> Classifier b b' -> Classifier (add a b) (add a' b'))
    (negCongr : forall {a b : BHist}, Classifier a b -> Classifier (neg a) (neg b))
    (mulCongr :
      forall {a a' b b' : BHist},
        Classifier a a' -> Classifier b b' -> Classifier (mul a b) (mul a' b'))
    (zeroAddZero : Classifier (add zero zero) zero)
    (addRegroup :
      forall {x y x' y' : BHist},
        Carrier x -> Carrier y -> Carrier x' -> Carrier y' ->
          Classifier (add (add x y) (add x' y')) (add (add x x') (add y y')))
    (negAdd :
      forall {x y : BHist}, Carrier x -> Carrier y ->
        Classifier (neg (add x y)) (add (neg x) (neg y)))
    (mulSumExpansion :
      forall {x y x' y' : BHist},
        Carrier x -> Carrier y -> Carrier x' -> Carrier y' ->
          Classifier (mul (add x y) (add x' y'))
            (add (add (mul x x') (add (mul x y') (mul y x'))) (mul y y')))
    (mulLeftDistrib :
      forall {r x y : BHist}, Carrier r -> Carrier x -> Carrier y ->
        Classifier (mul r (add x y)) (add (mul r x) (mul r y)))
    (mulRightDistrib :
      forall {x y r : BHist}, Carrier x -> Carrier y -> Carrier r ->
        Classifier (mul (add x y) r) (add (mul x r) (mul y r))) :
    let K : BHist -> Prop :=
      fun z => exists x : BHist, exists y : BHist, I x ∧ J y ∧ Classifier z (add x y)
    (forall {z : BHist}, K z -> Carrier z) ∧
      K zero ∧
      (forall {z w : BHist}, K z -> K w -> K (add z w)) ∧
      (forall {z : BHist}, K z -> K (neg z)) ∧
      (forall {z w : BHist}, K z -> K w -> K (mul z w)) ∧
      (forall {z z' : BHist}, K z -> Classifier z z' -> K z') ∧
      (forall {r z : BHist}, Carrier r -> K z -> K (mul r z) ∧ K (mul z r)) := by
  constructor
  · intro z memberZ
    cases memberZ with
    | intro x xRows =>
        cases xRows with
        | intro y rows =>
            have carrierX : Carrier x := I_support rows.left
            have carrierY : Carrier y := J_support rows.right.left
            have carrierSum : Carrier (add x y) := carrierAdd carrierX carrierY
            exact NameCert.carrier_respects_equiv cert
              (NameCert.equiv_symm cert rows.right.right) carrierSum
  · constructor
    · exact Exists.intro zero (Exists.intro zero
        (And.intro I_zero (And.intro J_zero (NameCert.equiv_symm cert zeroAddZero))))
    · constructor
      · intro z w memberZ memberW
        cases memberZ with
        | intro x xRows =>
            cases xRows with
            | intro y zRows =>
                cases memberW with
                | intro x' x'Rows =>
                    cases x'Rows with
                    | intro y' wRows =>
                        have carrierX : Carrier x := I_support zRows.left
                        have carrierY : Carrier y := J_support zRows.right.left
                        have carrierX' : Carrier x' := I_support wRows.left
                        have carrierY' : Carrier y' := J_support wRows.right.left
                        have firstStep :
                            Classifier (add z w) (add (add x y) (add x' y')) :=
                          addCongr zRows.right.right wRows.right.right
                        have regroupStep :
                            Classifier (add (add x y) (add x' y'))
                              (add (add x x') (add y y')) :=
                          addRegroup carrierX carrierY carrierX' carrierY'
                        exact Exists.intro (add x x') (Exists.intro (add y y')
                          (And.intro (I_add zRows.left wRows.left)
                            (And.intro (J_add zRows.right.left wRows.right.left)
                              (NameCert.equiv_trans cert firstStep regroupStep))))
      · constructor
        · intro z memberZ
          cases memberZ with
          | intro x xRows =>
              cases xRows with
              | intro y rows =>
                  have carrierX : Carrier x := I_support rows.left
                  have carrierY : Carrier y := J_support rows.right.left
                  have firstStep : Classifier (neg z) (neg (add x y)) :=
                    negCongr rows.right.right
                  have negStep : Classifier (neg (add x y)) (add (neg x) (neg y)) :=
                    negAdd carrierX carrierY
                  exact Exists.intro (neg x) (Exists.intro (neg y)
                    (And.intro (I_neg rows.left)
                      (And.intro (J_neg rows.right.left)
                        (NameCert.equiv_trans cert firstStep negStep))))
        · constructor
          · intro z w memberZ memberW
            cases memberZ with
            | intro x xRows =>
                cases xRows with
                | intro y zRows =>
                    cases memberW with
                    | intro x' x'Rows =>
                        cases x'Rows with
                        | intro y' wRows =>
                            have carrierX : Carrier x := I_support zRows.left
                            have carrierY : Carrier y := J_support zRows.right.left
                            have carrierX' : Carrier x' := I_support wRows.left
                            have carrierY' : Carrier y' := J_support wRows.right.left
                            have firstStep :
                                Classifier (mul z w) (mul (add x y) (add x' y')) :=
                              mulCongr zRows.right.right wRows.right.right
                            have expansion :
                                Classifier (mul (add x y) (add x' y'))
                                  (add (add (mul x x') (add (mul x y') (mul y x')))
                                    (mul y y')) :=
                              mulSumExpansion carrierX carrierY carrierX' carrierY'
                            have iXY' : I (mul x y') :=
                              (I_absorb carrierY' zRows.left).right
                            have iYX' : I (mul y x') :=
                              (I_absorb carrierY wRows.left).left
                            have iPart : I (add (mul x x') (add (mul x y') (mul y x'))) :=
                              I_add (I_mul zRows.left wRows.left) (I_add iXY' iYX')
                            exact Exists.intro (add (mul x x') (add (mul x y') (mul y x')))
                              (Exists.intro (mul y y')
                                (And.intro iPart
                                  (And.intro (J_mul zRows.right.left wRows.right.left)
                                    (NameCert.equiv_trans cert firstStep expansion))))
          · constructor
            · intro z z' memberZ classifiedZZ'
              cases memberZ with
              | intro x xRows =>
                  cases xRows with
                  | intro y rows =>
                      have classifiedZ'Z : Classifier z' z :=
                        NameCert.equiv_symm cert classifiedZZ'
                      exact Exists.intro x (Exists.intro y
                        (And.intro rows.left
                          (And.intro rows.right.left
                            (NameCert.equiv_trans cert classifiedZ'Z rows.right.right))))
            · intro r z carrierR memberZ
              cases memberZ with
              | intro x xRows =>
                  cases xRows with
                  | intro y rows =>
                      have carrierX : Carrier x := I_support rows.left
                      have carrierY : Carrier y := J_support rows.right.left
                      have reflR : Classifier r r :=
                        NameCert.equiv_refl cert carrierR
                      have leftFirst : Classifier (mul r z) (mul r (add x y)) :=
                        mulCongr reflR rows.right.right
                      have leftDistrib :
                          Classifier (mul r (add x y)) (add (mul r x) (mul r y)) :=
                        mulLeftDistrib carrierR carrierX carrierY
                      have rightFirst : Classifier (mul z r) (mul (add x y) r) :=
                        mulCongr rows.right.right reflR
                      have rightDistrib :
                          Classifier (mul (add x y) r) (add (mul x r) (mul y r)) :=
                        mulRightDistrib carrierX carrierY carrierR
                      constructor
                      · exact Exists.intro (mul r x) (Exists.intro (mul r y)
                          (And.intro (I_absorb carrierR rows.left).left
                            (And.intro (J_absorb carrierR rows.right.left).left
                              (NameCert.equiv_trans cert leftFirst leftDistrib))))
                      · exact Exists.intro (mul x r) (Exists.intro (mul y r)
                          (And.intro (I_absorb carrierR rows.left).right
                            (And.intro (J_absorb carrierR rows.right.left).right
                              (NameCert.equiv_trans cert rightFirst rightDistrib))))

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

def RingMapZeroFiber (CarrierS : BHist -> Prop) (ClassifierT : BHist -> BHist -> Prop)
    (f : BHist -> BHist) (zeroT x : BHist) : Prop :=
  CarrierS x ∧ ClassifierT (f x) zeroT

theorem RingMapZeroFiber_ideal_closure_rows
    {CarrierS CarrierT : BHist -> Prop}
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
    (mapNeg : forall {x : BHist}, CarrierS x -> ClassifierT (f (negS x)) (negT (f x)))
    (mapMul :
      forall {x y : BHist}, CarrierS x -> CarrierS y ->
        ClassifierT (f (mulS x y)) (mulT (f x) (f y)))
    (targetAddZero :
      forall {x y : BHist}, ClassifierT (f x) zeroT -> ClassifierT (f y) zeroT ->
        ClassifierT (addT (f x) (f y)) zeroT)
    (targetNegZero :
      forall {x : BHist}, ClassifierT (f x) zeroT -> ClassifierT (negT (f x)) zeroT)
    (targetMulZeroLeft :
      forall {r x : BHist}, CarrierS r -> ClassifierT (f x) zeroT ->
        ClassifierT (mulT (f r) (f x)) zeroT)
    (targetMulZeroRight :
      forall {r x : BHist}, CarrierS r -> ClassifierT (f x) zeroT ->
        ClassifierT (mulT (f x) (f r)) zeroT) :
    (forall {x : BHist}, RingMapZeroFiber CarrierS ClassifierT f zeroT x -> CarrierS x) ∧
      RingMapZeroFiber CarrierS ClassifierT f zeroT zeroS ∧
      (forall {x y : BHist},
        RingMapZeroFiber CarrierS ClassifierT f zeroT x ->
          RingMapZeroFiber CarrierS ClassifierT f zeroT y ->
            RingMapZeroFiber CarrierS ClassifierT f zeroT (addS x y)) ∧
      (forall {x : BHist},
        RingMapZeroFiber CarrierS ClassifierT f zeroT x ->
          RingMapZeroFiber CarrierS ClassifierT f zeroT (negS x)) ∧
      (forall {x y : BHist},
        RingMapZeroFiber CarrierS ClassifierT f zeroT x ->
          RingMapZeroFiber CarrierS ClassifierT f zeroT y ->
            RingMapZeroFiber CarrierS ClassifierT f zeroT (mulS x y)) ∧
      (forall {x y : BHist},
        RingMapZeroFiber CarrierS ClassifierT f zeroT x -> ClassifierS x y ->
          RingMapZeroFiber CarrierS ClassifierT f zeroT y) ∧
      (forall {r x : BHist},
        CarrierS r -> RingMapZeroFiber CarrierS ClassifierT f zeroT x ->
          RingMapZeroFiber CarrierS ClassifierT f zeroT (mulS r x) ∧
            RingMapZeroFiber CarrierS ClassifierT f zeroT (mulS x r)) := by
  constructor
  · intro x zeroFiberX
    exact zeroFiberX.left
  · constructor
    · have imageZeroSelf : ClassifierT (f zeroS) (f zeroS) :=
        NameCert.equiv_refl targetCert (mapCarrier sourceZero)
      exact And.intro sourceZero (NameCert.equiv_trans targetCert imageZeroSelf mapZero)
    · constructor
      · intro x y zeroFiberX zeroFiberY
        have carrierAdd : CarrierS (addS x y) := sourceAdd zeroFiberX.left zeroFiberY.left
        have mapAddClassified : ClassifierT (f (addS x y)) (addT (f x) (f y)) :=
          mapAdd zeroFiberX.left zeroFiberY.left
        have targetZeroClassified : ClassifierT (addT (f x) (f y)) zeroT :=
          targetAddZero zeroFiberX.right zeroFiberY.right
        exact And.intro carrierAdd
          (NameCert.equiv_trans targetCert mapAddClassified targetZeroClassified)
      · constructor
        · intro x zeroFiberX
          have carrierNeg : CarrierS (negS x) := sourceNeg zeroFiberX.left
          have mapNegClassified : ClassifierT (f (negS x)) (negT (f x)) :=
            mapNeg zeroFiberX.left
          have targetZeroClassified : ClassifierT (negT (f x)) zeroT :=
            targetNegZero zeroFiberX.right
          exact And.intro carrierNeg
            (NameCert.equiv_trans targetCert mapNegClassified targetZeroClassified)
        · constructor
          · intro x y zeroFiberX zeroFiberY
            have carrierMul : CarrierS (mulS x y) := sourceMul zeroFiberX.left zeroFiberY.left
            have mapMulClassified : ClassifierT (f (mulS x y)) (mulT (f x) (f y)) :=
              mapMul zeroFiberX.left zeroFiberY.left
            have targetZeroClassified : ClassifierT (mulT (f x) (f y)) zeroT :=
              targetMulZeroLeft zeroFiberX.left zeroFiberY.right
            exact And.intro carrierMul
              (NameCert.equiv_trans targetCert mapMulClassified targetZeroClassified)
          · constructor
            · intro x y zeroFiberX classifiedXY
              have carrierY : CarrierS y :=
                NameCert.carrier_respects_equiv sourceCert classifiedXY zeroFiberX.left
              have imageClassified : ClassifierT (f x) (f y) :=
                mapClassifier zeroFiberX.left carrierY classifiedXY
              have imageReverse : ClassifierT (f y) (f x) :=
                NameCert.equiv_symm targetCert imageClassified
              exact And.intro carrierY
                (NameCert.equiv_trans targetCert imageReverse zeroFiberX.right)
            · intro r x carrierR zeroFiberX
              have carrierLeft : CarrierS (mulS r x) := sourceMul carrierR zeroFiberX.left
              have mapLeft : ClassifierT (f (mulS r x)) (mulT (f r) (f x)) :=
                mapMul carrierR zeroFiberX.left
              have zeroLeft : ClassifierT (mulT (f r) (f x)) zeroT :=
                targetMulZeroLeft carrierR zeroFiberX.right
              have carrierRight : CarrierS (mulS x r) := sourceMul zeroFiberX.left carrierR
              have mapRight : ClassifierT (f (mulS x r)) (mulT (f x) (f r)) :=
                mapMul zeroFiberX.left carrierR
              have zeroRight : ClassifierT (mulT (f x) (f r)) zeroT :=
                targetMulZeroRight carrierR zeroFiberX.right
              exact And.intro
                (And.intro carrierLeft (NameCert.equiv_trans targetCert mapLeft zeroLeft))
                (And.intro carrierRight (NameCert.equiv_trans targetCert mapRight zeroRight))

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

theorem IdealZeroPredicate_ideal_closure
    {Carrier : BHist -> Prop} {Classifier : BHist -> BHist -> Prop}
    {zero : BHist}
    {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist}
    (cert : NameCert Carrier Classifier)
    (zeroCarrier : Carrier zero)
    (addClosed : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (add x y))
    (negClosed : forall {x : BHist}, Carrier x -> Carrier (neg x))
    (mulClosed : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (mul x y))
    (zeroClassified : Classifier zero zero)
    (addZeroClosed :
      forall {x y : BHist}, Classifier x zero -> Classifier y zero ->
        Classifier (add x y) zero)
    (negZeroClosed : forall {x : BHist}, Classifier x zero -> Classifier (neg x) zero)
    (mulZeroClosed :
      forall {x y : BHist}, Classifier x zero -> Classifier y zero ->
        Classifier (mul x y) zero)
    (zeroTransport :
      forall {x y : BHist}, Classifier x zero -> Classifier x y -> Classifier y zero)
    (leftAbsorbZero :
      forall {r x : BHist}, Carrier r -> Classifier x zero -> Classifier (mul r x) zero)
    (rightAbsorbZero :
      forall {r x : BHist}, Carrier r -> Classifier x zero -> Classifier (mul x r) zero) :
    (forall {x : BHist}, (Carrier x ∧ Classifier x zero) -> Carrier x) ∧
      (Carrier zero ∧ Classifier zero zero) ∧
      (forall {x y : BHist}, (Carrier x ∧ Classifier x zero) ->
        (Carrier y ∧ Classifier y zero) ->
          Carrier (add x y) ∧ Classifier (add x y) zero) ∧
      (forall {x : BHist}, (Carrier x ∧ Classifier x zero) ->
        Carrier (neg x) ∧ Classifier (neg x) zero) ∧
      (forall {x y : BHist}, (Carrier x ∧ Classifier x zero) ->
        (Carrier y ∧ Classifier y zero) ->
          Carrier (mul x y) ∧ Classifier (mul x y) zero) ∧
      (forall {x y : BHist}, (Carrier x ∧ Classifier x zero) ->
        Classifier x y -> Carrier y ∧ Classifier y zero) ∧
      (forall {r x : BHist}, Carrier r -> (Carrier x ∧ Classifier x zero) ->
        (Carrier (mul r x) ∧ Classifier (mul r x) zero) ∧
          (Carrier (mul x r) ∧ Classifier (mul x r) zero)) := by
  constructor
  · intro x zeroIdealX
    exact zeroIdealX.left
  · constructor
    · exact And.intro zeroCarrier zeroClassified
    · constructor
      · intro x y zeroIdealX zeroIdealY
        exact And.intro (addClosed zeroIdealX.left zeroIdealY.left)
          (addZeroClosed zeroIdealX.right zeroIdealY.right)
      · constructor
        · intro x zeroIdealX
          exact And.intro (negClosed zeroIdealX.left) (negZeroClosed zeroIdealX.right)
        · constructor
          · intro x y zeroIdealX zeroIdealY
            exact And.intro (mulClosed zeroIdealX.left zeroIdealY.left)
              (mulZeroClosed zeroIdealX.right zeroIdealY.right)
          · constructor
            · intro x y zeroIdealX classifiedXY
              have carrierY : Carrier y :=
                NameCert.carrier_respects_equiv cert classifiedXY zeroIdealX.left
              exact And.intro carrierY (zeroTransport zeroIdealX.right classifiedXY)
            · intro r x carrierR zeroIdealX
              exact And.intro
                (And.intro (mulClosed carrierR zeroIdealX.left)
                  (leftAbsorbZero carrierR zeroIdealX.right))
                (And.intro (mulClosed zeroIdealX.left carrierR)
                  (rightAbsorbZero carrierR zeroIdealX.right))

theorem IdealQuotientKernel_diagonal_exactness
    {Carrier I : BHist -> Prop} {Classifier : BHist -> BHist -> Prop}
    {zero : BHist} {sub : BHist -> BHist -> BHist}
    (cert : NameCert Carrier Classifier)
    (idealZero : I zero)
    (idealTransport : forall {u v : BHist}, I u -> Classifier u v -> I v)
    (subDiagonal : forall {x : BHist}, Carrier x -> Classifier (sub x x) zero)
    {x : BHist} :
    Carrier x -> Carrier x ∧ Carrier x ∧ I (sub x x) := by
  intro carrierX
  have sameZeroSub : Classifier zero (sub x x) :=
    NameCert.equiv_symm cert (subDiagonal carrierX)
  exact And.intro carrierX (And.intro carrierX (idealTransport idealZero sameZeroSub))

theorem IdealQuotientKernel_endpoint_transport
    {Carrier I : BHist -> Prop} {Classifier : BHist -> BHist -> Prop}
    {sub : BHist -> BHist -> BHist}
    (cert : NameCert Carrier Classifier)
    (subCongr :
      forall {x x' y y' : BHist}, Classifier x x' -> Classifier y y' ->
        Classifier (sub x y) (sub x' y'))
    (I_transport : forall {u v : BHist}, I u -> Classifier u v -> I v)
    {x y x' y' : BHist} :
    (Carrier x ∧ Carrier y ∧ I (sub x y)) ->
      Classifier x x' -> Classifier y y' ->
        Carrier x' ∧ Carrier y' ∧ I (sub x' y') := by
  intro kernelXY classifiedXX classifiedYY
  have carrierX' : Carrier x' :=
    NameCert.carrier_respects_equiv cert classifiedXX kernelXY.left
  have carrierY' : Carrier y' :=
    NameCert.carrier_respects_equiv cert classifiedYY kernelXY.right.left
  have classifiedSub : Classifier (sub x y) (sub x' y') :=
    subCongr classifiedXX classifiedYY
  exact And.intro carrierX' (And.intro carrierY' (I_transport kernelXY.right.right classifiedSub))

end BEDC.Derived.IdealUp
