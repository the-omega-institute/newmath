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

end BEDC.Derived.IdealUp
