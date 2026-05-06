import BEDC.Derived.IdealUp

namespace BEDC.Derived.IdealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def IdealQuotientKernelSource (Carrier I : BHist -> Prop)
    (Classifier : BHist -> BHist -> Prop) (sub : BHist -> BHist -> BHist)
    (x y : BHist) : Prop :=
  NameCert Carrier Classifier ∧ Carrier x ∧ Carrier y ∧ I (sub x y)

theorem IdealAmbientCarrier_quotient_kernel_exactness
    {Carrier : BHist -> Prop} {sub : BHist -> BHist -> BHist}
    (subCarrier : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (sub x y))
    {x y : BHist} :
    ((Carrier x ∧ Carrier y ∧ Carrier (sub x y)) <-> (Carrier x ∧ Carrier y)) := by
  constructor
  · intro kernelRows
    exact And.intro kernelRows.left kernelRows.right.left
  · intro carrierRows
    exact And.intro carrierRows.left
      (And.intro carrierRows.right (subCarrier carrierRows.left carrierRows.right))

theorem IdealQuotientKernel_multiplication_descent
    {Carrier I : BHist -> Prop} {Classifier : BHist -> BHist -> Prop}
    {mul sub add : BHist -> BHist -> BHist}
    (mulCarrier : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (mul x y))
    (idealAdd : forall {x y : BHist}, I x -> I y -> I (add x y))
    (idealTransport : forall {x y : BHist}, I x -> Classifier x y -> I y)
    (idealLeftAbsorb : forall {r x : BHist}, Carrier r -> I x -> I (mul r x))
    (idealRightAbsorb : forall {r x : BHist}, Carrier r -> I x -> I (mul x r))
    (productDifference :
      forall {a a' b b' : BHist},
        Carrier a -> Carrier a' -> Carrier b -> Carrier b' ->
          Classifier (add (mul (sub a a') b) (mul a' (sub b b')))
            (sub (mul a b) (mul a' b')))
    {a a' b b' : BHist} :
    (Carrier a ∧ Carrier a' ∧ I (sub a a')) ->
      (Carrier b ∧ Carrier b' ∧ I (sub b b')) ->
        Carrier (mul a b) ∧ Carrier (mul a' b') ∧
          I (sub (mul a b) (mul a' b')) := by
  intro leftKernel rightKernel
  have carrierA : Carrier a := leftKernel.left
  have carrierA' : Carrier a' := leftKernel.right.left
  have carrierB : Carrier b := rightKernel.left
  have carrierB' : Carrier b' := rightKernel.right.left
  have firstDifference : I (mul (sub a a') b) :=
    idealRightAbsorb carrierB leftKernel.right.right
  have secondDifference : I (mul a' (sub b b')) :=
    idealLeftAbsorb carrierA' rightKernel.right.right
  have displayedDifference :
      I (add (mul (sub a a') b) (mul a' (sub b b'))) :=
    idealAdd firstDifference secondDifference
  exact And.intro (mulCarrier carrierA carrierB)
    (And.intro (mulCarrier carrierA' carrierB')
      (idealTransport displayedDifference
        (productDifference carrierA carrierA' carrierB carrierB')))

theorem IdealQuotientKernel_export_surface
    {Carrier I : BHist -> Prop} {Classifier : BHist -> BHist -> Prop} {zero : BHist}
    {add mul sub : BHist -> BHist -> BHist} {neg : BHist -> BHist}
    (cert : NameCert Carrier Classifier)
    (carrierAdd : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (add x y))
    (carrierNeg : forall {x : BHist}, Carrier x -> Carrier (neg x))
    (mulCarrier : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (mul x y))
    (idealZero : I zero)
    (idealAdd : forall {x y : BHist}, I x -> I y -> I (add x y))
    (idealNeg : forall {x : BHist}, I x -> I (neg x))
    (idealTransport : forall {x y : BHist}, I x -> Classifier x y -> I y)
    (idealAbsorb :
      forall {r x : BHist}, Carrier r -> I x -> I (mul r x) ∧ I (mul x r))
    (subDiagonal : forall {x : BHist}, Carrier x -> Classifier (sub x x) zero)
    (subCongr :
      forall {x x' y y' : BHist}, Classifier x x' -> Classifier y y' ->
        Classifier (sub x y) (sub x' y'))
    (addSubClassified :
      forall {a a' b b' : BHist}, Carrier a -> Carrier a' -> Carrier b -> Carrier b' ->
        Classifier (add (sub a a') (sub b b')) (sub (add a b) (add a' b')))
    (negSubClassified :
      forall {a a' : BHist}, Carrier a -> Carrier a' ->
        Classifier (neg (sub a a')) (sub (neg a) (neg a')))
    (productDifference :
      forall {a a' b b' : BHist}, Carrier a -> Carrier a' -> Carrier b -> Carrier b' ->
        Classifier (add (mul (sub a a') b) (mul a' (sub b b')))
          (sub (mul a b) (mul a' b'))) :
    (forall {x : BHist}, Carrier x -> Carrier x ∧ Carrier x ∧ I (sub x x)) ∧
      (forall {x y x' y' : BHist},
        (Carrier x ∧ Carrier y ∧ I (sub x y)) -> Classifier x x' -> Classifier y y' ->
          Carrier x' ∧ Carrier y' ∧ I (sub x' y')) ∧
      (forall {a a' b b' : BHist},
        (Carrier a ∧ Carrier a' ∧ I (sub a a')) ->
          (Carrier b ∧ Carrier b' ∧ I (sub b b')) ->
            Carrier (add a b) ∧ Carrier (add a' b') ∧
              I (sub (add a b) (add a' b'))) ∧
      (forall {a a' : BHist},
        (Carrier a ∧ Carrier a' ∧ I (sub a a')) ->
          Carrier (neg a) ∧ Carrier (neg a') ∧ I (sub (neg a) (neg a'))) ∧
      (forall {a a' b b' : BHist},
        (Carrier a ∧ Carrier a' ∧ I (sub a a')) ->
          (Carrier b ∧ Carrier b' ∧ I (sub b b')) ->
            Carrier (mul a b) ∧ Carrier (mul a' b') ∧
              I (sub (mul a b) (mul a' b'))) := by
  constructor
  · intro x carrierX
    exact IdealQuotientKernel_diagonal_exactness cert idealZero idealTransport
      subDiagonal carrierX
  · constructor
    · intro x y x' y' kernelXY classifiedXX' classifiedYY'
      exact IdealQuotientKernel_endpoint_transport cert subCongr idealTransport
        kernelXY classifiedXX' classifiedYY'
    · constructor
      · intro a a' b b' kernelAA' kernelBB'
        have carrierA : Carrier a := kernelAA'.left
        have carrierA' : Carrier a' := kernelAA'.right.left
        have carrierB : Carrier b := kernelBB'.left
        have carrierB' : Carrier b' := kernelBB'.right.left
        have combinedIdeal : I (add (sub a a') (sub b b')) :=
          idealAdd kernelAA'.right.right kernelBB'.right.right
        have sameCombined :
            Classifier (add (sub a a') (sub b b'))
              (sub (add a b) (add a' b')) :=
          addSubClassified carrierA carrierA' carrierB carrierB'
        exact And.intro (carrierAdd carrierA carrierB)
          (And.intro (carrierAdd carrierA' carrierB')
            (idealTransport combinedIdeal sameCombined))
      · constructor
        · intro a a' kernelAA'
          have carrierA : Carrier a := kernelAA'.left
          have carrierA' : Carrier a' := kernelAA'.right.left
          have negIdeal : I (neg (sub a a')) := idealNeg kernelAA'.right.right
          have sameNeg :
              Classifier (neg (sub a a')) (sub (neg a) (neg a')) :=
            negSubClassified carrierA carrierA'
          exact And.intro (carrierNeg carrierA)
            (And.intro (carrierNeg carrierA') (idealTransport negIdeal sameNeg))
        · intro a a' b b' kernelAA' kernelBB'
          exact IdealQuotientKernel_multiplication_descent
            (Carrier := Carrier) (I := I) (Classifier := Classifier)
            (mul := mul) (sub := sub) (add := add)
            mulCarrier idealAdd idealTransport
            (fun carrierR idealX => (idealAbsorb carrierR idealX).left)
            (fun carrierR idealX => (idealAbsorb carrierR idealX).right)
            productDifference (a := a) (a' := a') (b := b) (b' := b')
            kernelAA' kernelBB'

end BEDC.Derived.IdealUp
