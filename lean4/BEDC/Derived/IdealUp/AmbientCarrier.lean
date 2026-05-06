import BEDC.Derived.IdealUp

namespace BEDC.Derived.IdealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem IdealAmbientCarrier_closure_rows
    {Carrier : BHist -> Prop}
    {Classifier : BHist -> BHist -> Prop}
    {zero : BHist}
    {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist}
    (cert : NameCert Carrier Classifier)
    (carrierZero : Carrier zero)
    (carrierAdd : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (add x y))
    (carrierNeg : forall {x : BHist}, Carrier x -> Carrier (neg x))
    (carrierMul : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (mul x y)) :
    (forall {x : BHist}, Carrier x -> Carrier x) ∧
      Carrier zero ∧
      (forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (add x y)) ∧
      (forall {x : BHist}, Carrier x -> Carrier (neg x)) ∧
      (forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (mul x y)) ∧
      (forall {x y : BHist}, Carrier x -> Classifier x y -> Carrier y) ∧
      (forall {r x : BHist}, Carrier r -> Carrier x ->
        Carrier (mul r x) ∧ Carrier (mul x r)) := by
  constructor
  · intro x carrierX
    exact NameCert.carrier_respects_equiv cert (NameCert.equiv_refl cert carrierX) carrierX
  · constructor
    · exact carrierZero
    · constructor
      · intro x y carrierX carrierY
        exact carrierAdd carrierX carrierY
      · constructor
        · intro x carrierX
          exact carrierNeg carrierX
        · constructor
          · intro x y carrierX carrierY
            exact carrierMul carrierX carrierY
          · constructor
            · intro x y carrierX classified
              exact NameCert.carrier_respects_equiv cert classified carrierX
            · intro r x carrierR carrierX
              exact And.intro (carrierMul carrierR carrierX) (carrierMul carrierX carrierR)

end BEDC.Derived.IdealUp
