import BEDC.Derived.IdealUp

namespace BEDC.Derived.IdealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem IdealZeroAndWholeQuotientKernel_scope
    {Carrier : BHist -> Prop} {Classifier : BHist -> BHist -> Prop}
    {zero : BHist} {add : BHist -> BHist -> BHist} {neg : BHist -> BHist}
    (cert : NameCert Carrier Classifier)
    (negClosed : forall {x : BHist}, Carrier x -> Carrier (neg x))
    (addClosed : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (add x y))
    (zeroTransport :
      forall {x y : BHist}, Carrier x -> Carrier y -> Classifier x zero -> Classifier y zero) :
    (forall {x y : BHist},
        Carrier x -> Carrier y -> Carrier x ∧ Carrier y ∧ Carrier (add x (neg y))) ∧
      (forall {x y : BHist},
        Carrier x ∧ Carrier y ∧ Carrier (add x (neg y)) -> Carrier x ∧ Carrier y) := by
  have certifiedTransport :
      NameCert Carrier Classifier ∧
        (forall {x y : BHist}, Carrier x -> Carrier y -> Classifier x zero ->
          Classifier y zero) :=
    And.intro cert zeroTransport
  cases certifiedTransport with
  | intro _ _ =>
      constructor
      · intro x y carrierX carrierY
        exact And.intro carrierX (And.intro carrierY (addClosed carrierX (negClosed carrierY)))
      · intro x y kernelXY
        exact And.intro kernelXY.left kernelXY.right.left

theorem IdealQuotientKernel_product_difference_membership
    {Carrier I : BHist -> Prop} {Classifier : BHist -> BHist -> Prop}
    {add mul sub : BHist -> BHist -> BHist} {a a' b b' : BHist}
    (cert : NameCert Carrier Classifier)
    (idealAdd : forall {x y : BHist}, I x -> I y -> I (add x y))
    (idealTransport : forall {x y : BHist}, I x -> Classifier x y -> I y)
    (idealAbsorb :
      forall {r x : BHist}, Carrier r -> I x -> I (mul r x) ∧ I (mul x r))
    (productDifference :
      Classifier (add (mul (sub a a') b) (mul a' (sub b b')))
        (sub (mul a b) (mul a' b'))) :
    Carrier b -> Carrier a' -> I (sub a a') -> I (sub b b') ->
      I (sub (mul a b) (mul a' b')) := by
  intro carrierB carrierA' diffA diffB
  have _certified : NameCert Carrier Classifier := cert
  have rightAbsorbed : I (mul (sub a a') b) :=
    (idealAbsorb carrierB diffA).right
  have leftAbsorbed : I (mul a' (sub b b')) :=
    (idealAbsorb carrierA' diffB).left
  exact idealTransport (idealAdd rightAbsorbed leftAbsorbed) productDifference

end BEDC.Derived.IdealUp
