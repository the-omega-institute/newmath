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

theorem IdealCarriedPredicateRows_support_transport_surface
    {Carrier I : BHist -> Prop} {Classifier : BHist -> BHist -> Prop} {zero : BHist}
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist}
    {cert : NameCert Carrier Classifier}
    (rows : IdealCarriedPredicateRows Carrier I Classifier zero add mul neg cert) :
    (forall {x : BHist}, I x -> Carrier x) ∧
      (forall {x y : BHist}, I x -> Classifier x y -> Carrier y ∧ I y) := by
  constructor
  · exact rows.support
  · intro x y memberX sameXY
    have carrierX : Carrier x := rows.support memberX
    have carrierY : Carrier y := cert.carrier_respects_equiv sameXY carrierX
    have memberY : I y := rows.transport memberX sameXY
    exact And.intro carrierY memberY

theorem IdealCarriedPredicateRows_classifier_absorption_surface
    {Carrier I : BHist -> Prop} {Classifier : BHist -> BHist -> Prop} {zero : BHist}
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist}
    {cert : NameCert Carrier Classifier}
    (rows : IdealCarriedPredicateRows Carrier I Classifier zero add mul neg cert) :
    (forall {x y : BHist}, I x -> Classifier x y -> I y) ∧
      (forall {r x : BHist}, Carrier r -> I x ->
        Carrier (mul r x) ∧ I (mul r x) ∧ Carrier (mul x r) ∧ I (mul x r)) := by
  constructor
  · exact rows.transport
  · intro r x carrierR memberX
    have absorbed : I (mul r x) ∧ I (mul x r) := rows.absorb carrierR memberX
    have carrierLeft : Carrier (mul r x) := rows.support absorbed.left
    have carrierRight : Carrier (mul x r) := rows.support absorbed.right
    exact And.intro carrierLeft
      (And.intro absorbed.left (And.intro carrierRight absorbed.right))

end BEDC.Derived.IdealUp
