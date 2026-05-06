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

theorem IdealZeroPredicate_closure_rows
    {Carrier : BHist -> Prop}
    {Classifier : BHist -> BHist -> Prop}
    {zero : BHist}
    {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist}
    (cert : NameCert Carrier Classifier)
    (carrierZero : Carrier zero)
    (carrierAdd : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (add x y))
    (carrierNeg : forall {x : BHist}, Carrier x -> Carrier (neg x))
    (carrierMul : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (mul x y))
    (addCongr :
      forall {a a' b b' : BHist},
        Classifier a a' -> Classifier b b' -> Classifier (add a b) (add a' b'))
    (negCongr : forall {a b : BHist}, Classifier a b -> Classifier (neg a) (neg b))
    (mulCongr :
      forall {a a' b b' : BHist},
        Classifier a a' -> Classifier b b' -> Classifier (mul a b) (mul a' b'))
    (zeroAddZero : Classifier (add zero zero) zero)
    (negZero : Classifier (neg zero) zero)
    (mulZeroLeft : forall {r : BHist}, Carrier r -> Classifier (mul zero r) zero)
    (mulZeroRight : forall {r : BHist}, Carrier r -> Classifier (mul r zero) zero) :
    let ZeroPredicate : BHist -> Prop := fun x => Carrier x ∧ Classifier x zero
    (forall {x : BHist}, ZeroPredicate x -> Carrier x) ∧
      ZeroPredicate zero ∧
      (forall {x y : BHist},
        ZeroPredicate x -> ZeroPredicate y -> ZeroPredicate (add x y)) ∧
      (forall {x : BHist}, ZeroPredicate x -> ZeroPredicate (neg x)) ∧
      (forall {x y : BHist},
        ZeroPredicate x -> ZeroPredicate y -> ZeroPredicate (mul x y)) ∧
      (forall {x y : BHist}, ZeroPredicate x -> Classifier x y -> ZeroPredicate y) ∧
      (forall {r x : BHist},
        Carrier r -> ZeroPredicate x ->
          ZeroPredicate (mul r x) ∧ ZeroPredicate (mul x r)) := by
  constructor
  · intro x zeroX
    exact zeroX.left
  · constructor
    · exact And.intro carrierZero (NameCert.equiv_refl cert carrierZero)
    · constructor
      · intro x y zeroX zeroY
        have addClassified : Classifier (add x y) (add zero zero) :=
          addCongr zeroX.right zeroY.right
        exact And.intro (carrierAdd zeroX.left zeroY.left)
          (NameCert.equiv_trans cert addClassified zeroAddZero)
      · constructor
        · intro x zeroX
          have negClassified : Classifier (neg x) (neg zero) :=
            negCongr zeroX.right
          exact And.intro (carrierNeg zeroX.left)
            (NameCert.equiv_trans cert negClassified negZero)
        · constructor
          · intro x y zeroX zeroY
            have mulClassified : Classifier (mul x y) (mul zero zero) :=
              mulCongr zeroX.right zeroY.right
            exact And.intro (carrierMul zeroX.left zeroY.left)
              (NameCert.equiv_trans cert mulClassified (mulZeroLeft carrierZero))
          · constructor
            · intro x y zeroX classifiedXY
              have classifiedYX : Classifier y x :=
                NameCert.equiv_symm cert classifiedXY
              exact And.intro (NameCert.carrier_respects_equiv cert classifiedXY zeroX.left)
                (NameCert.equiv_trans cert classifiedYX zeroX.right)
            · intro r x carrierR zeroX
              have reflR : Classifier r r :=
                NameCert.equiv_refl cert carrierR
              constructor
              · have leftStep : Classifier (mul r x) (mul r zero) :=
                  mulCongr reflR zeroX.right
                exact And.intro (carrierMul carrierR zeroX.left)
                  (NameCert.equiv_trans cert leftStep (mulZeroRight carrierR))
              · have rightStep : Classifier (mul x r) (mul zero r) :=
                  mulCongr zeroX.right reflR
                exact And.intro (carrierMul zeroX.left carrierR)
                  (NameCert.equiv_trans cert rightStep (mulZeroLeft carrierR))

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

end BEDC.Derived.IdealUp
