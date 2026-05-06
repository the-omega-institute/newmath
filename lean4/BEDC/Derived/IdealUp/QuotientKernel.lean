import BEDC.Derived.IdealUp

namespace BEDC.Derived.IdealUp

open BEDC.FKernel.Hist

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

end BEDC.Derived.IdealUp
