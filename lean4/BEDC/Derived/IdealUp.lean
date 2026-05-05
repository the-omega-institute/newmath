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

end BEDC.Derived.IdealUp
