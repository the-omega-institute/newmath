import BEDC.Derived.IdealUp

namespace BEDC.Derived.IdealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem IdealQuotientKernel_absorption_closure
    {Carrier I : BHist -> Prop} {Classifier : BHist -> BHist -> Prop}
    {sub mul : BHist -> BHist -> BHist}
    (cert : NameCert Carrier Classifier)
    (mulCarrier : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (mul x y))
    (idealTransport : forall {u v : BHist}, I u -> Classifier u v -> I v)
    (idealAbsorb :
      forall {r x : BHist}, Carrier r -> I x -> I (mul r x) ∧ I (mul x r))
    (leftDiff :
      forall {r x y : BHist}, Carrier r -> Carrier x -> Carrier y ->
        Classifier (sub (mul r x) (mul r y)) (mul r (sub x y)))
    (rightDiff :
      forall {r x y : BHist}, Carrier r -> Carrier x -> Carrier y ->
        Classifier (sub (mul x r) (mul y r)) (mul (sub x y) r))
    {r x y : BHist} :
    Carrier r -> (Carrier x ∧ Carrier y ∧ I (sub x y)) ->
      (Carrier (mul r x) ∧ Carrier (mul r y) ∧
          I (sub (mul r x) (mul r y))) ∧
        (Carrier (mul x r) ∧ Carrier (mul y r) ∧
          I (sub (mul x r) (mul y r))) := by
  intro carrierR kernelXY
  have carrierX : Carrier x := kernelXY.left
  have carrierY : Carrier y := kernelXY.right.left
  have idealDiff : I (sub x y) := kernelXY.right.right
  have leftAbsorbed : I (mul r (sub x y)) :=
    (idealAbsorb carrierR idealDiff).left
  have rightAbsorbed : I (mul (sub x y) r) :=
    (idealAbsorb carrierR idealDiff).right
  have leftSame :
      Classifier (mul r (sub x y)) (sub (mul r x) (mul r y)) :=
    NameCert.equiv_symm cert (leftDiff carrierR carrierX carrierY)
  have rightSame :
      Classifier (mul (sub x y) r) (sub (mul x r) (mul y r)) :=
    NameCert.equiv_symm cert (rightDiff carrierR carrierX carrierY)
  constructor
  · exact And.intro (mulCarrier carrierR carrierX)
      (And.intro (mulCarrier carrierR carrierY)
        (idealTransport leftAbsorbed leftSame))
  · exact And.intro (mulCarrier carrierX carrierR)
      (And.intro (mulCarrier carrierY carrierR)
        (idealTransport rightAbsorbed rightSame))

end BEDC.Derived.IdealUp
