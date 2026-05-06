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

end BEDC.Derived.IdealUp
