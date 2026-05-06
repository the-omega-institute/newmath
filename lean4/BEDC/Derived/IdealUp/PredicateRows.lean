import BEDC.Derived.IdealUp

namespace BEDC.Derived.IdealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

structure IdealCarriedPredicateRows (Carrier I : BHist -> Prop)
    (Classifier : BHist -> BHist -> Prop) (zero : BHist)
    (add mul : BHist -> BHist -> BHist) (neg : BHist -> BHist)
    (cert : NameCert Carrier Classifier) where
  support : forall {x : BHist}, I x -> Carrier x
  zero_mem : I zero
  add_mem : forall {x y : BHist}, I x -> I y -> I (add x y)
  neg_mem : forall {x : BHist}, I x -> I (neg x)
  transport : forall {x y : BHist}, I x -> Classifier x y -> I y
  absorb : forall {r x : BHist}, Carrier r -> I x -> I (mul r x) ∧ I (mul x r)

structure IdealObligationInventory (Carrier I : BHist -> Prop)
    (Classifier : BHist -> BHist -> Prop) (zero : BHist)
    (add mul : BHist -> BHist -> BHist) (neg : BHist -> BHist) where
  cert : NameCert Carrier Classifier
  rows : IdealCarriedPredicateRows Carrier I Classifier zero add mul neg cert
  carrier_zero : Carrier zero
  add_carrier : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (add x y)
  neg_carrier : forall {x : BHist}, Carrier x -> Carrier (neg x)
  mul_carrier : forall {x y : BHist}, Carrier x -> Carrier y -> Carrier (mul x y)

theorem IdealCarriedPredicateRows_zero_add_neg_mul_rows
    {Carrier I : BHist -> Prop} {Classifier : BHist -> BHist -> Prop} {zero : BHist}
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist}
    {cert : NameCert Carrier Classifier}
    (rows : IdealCarriedPredicateRows Carrier I Classifier zero add mul neg cert) :
    I zero ∧
      (forall {x y : BHist}, I x -> I y -> I (add x y)) ∧
      (forall {x : BHist}, I x -> I (neg x)) ∧
      (forall {x y : BHist}, I x -> I y -> I (mul x y)) := by
  constructor
  · exact rows.zero_mem
  · constructor
    · exact rows.add_mem
    · constructor
      · exact rows.neg_mem
      · intro x y memberX memberY
        exact (rows.absorb (rows.support memberY) memberX).right

theorem IdealObligationInventory_classifier_absorption_rows
    {Carrier I : BHist -> Prop} {Classifier : BHist -> BHist -> Prop} {zero : BHist}
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist}
    (inventory : IdealObligationInventory Carrier I Classifier zero add mul neg) :
    NameCert Carrier Classifier ∧
      (forall {x y : BHist}, I x -> Classifier x y -> Carrier y ∧ I y) ∧
      (forall {r x : BHist}, Carrier r -> I x ->
        (Carrier (mul r x) ∧ I (mul r x)) ∧ (Carrier (mul x r) ∧ I (mul x r))) := by
  constructor
  · exact inventory.cert
  · constructor
    · intro x y memberX classified
      have carrierX : Carrier x := inventory.rows.support memberX
      have carrierY : Carrier y :=
        NameCert.carrier_respects_equiv inventory.cert classified carrierX
      exact And.intro carrierY (inventory.rows.transport memberX classified)
    · intro r x carrierR memberX
      have carrierX : Carrier x := inventory.rows.support memberX
      have absorbed := inventory.rows.absorb carrierR memberX
      exact And.intro
        (And.intro (inventory.mul_carrier carrierR carrierX) absorbed.left)
        (And.intro (inventory.mul_carrier carrierX carrierR) absorbed.right)

end BEDC.Derived.IdealUp
