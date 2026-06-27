import BEDC.Derived.CyclicGroupUp
import BEDC.Derived.PrimitiveRootFinal

namespace BEDC.Derived.PrimitiveRootCyclic

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.CyclicGroupUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.PrimitiveRootExistence
open BEDC.Derived.PrimitiveRootFinal
open BEDC.Derived.PrimitiveRootUp
open BEDC.Derived.ZModFieldUp
open BEDC.Derived.ZModResidueList
open BEDC.Derived.ZModUp

def orderLayer {p : BHist} (prime : NatPrime p) (k : BHist) : List (ZMod p) :=
  (nonzeroResidues prime).filter (fun x => bhistEqBool (orderOf prime x) k)

theorem topOrderLayer_eq_orderLayer {p : BHist} (prime : NatPrime p) :
    topOrderLayer prime = orderLayer prime (unaryPred p) := by
  rfl

theorem primitive_root_exists_from_topOrderLayer_nonempty {p : BHist}
    (prime : NatPrime p) :
    0 < (topOrderLayer prime).length ->
      ∃ g : ZMod p,
        zmodNonzero g ∧
          IsPrimitiveRoot p prime.left (NatPrime_empty_absurd prime)
            (unaryPred p) g := by
  intro layerPositive
  exact primitive_root_exists_of_topOrderLayer_pos prime layerPositive

def PrimitiveRootClosureBridge {p : BHist} (prime : NatPrime p) : Prop :=
  0 < (topOrderLayer prime).length

theorem primitive_root_exists_of_closure_bridge {p : BHist}
    (prime : NatPrime p) :
    PrimitiveRootClosureBridge prime ->
      ∃ g : ZMod p,
        zmodNonzero g ∧
          IsPrimitiveRoot p prime.left (NatPrime_empty_absurd prime)
            (unaryPred p) g := by
  intro bridge
  exact primitive_root_exists_from_topOrderLayer_nonempty prime bridge

def PrimeUnitGroupCyclic {p : BHist} (prime : NatPrime p) : Prop :=
  ∃ g : ZMod p,
    zmodNonzero g ∧
      IsPrimitiveRoot p prime.left (NatPrime_empty_absurd prime)
        (unaryPred p) g

theorem prime_unit_group_cyclic_of_closure_bridge {p : BHist}
    (prime : NatPrime p) :
    PrimitiveRootClosureBridge prime -> PrimeUnitGroupCyclic prime := by
  intro bridge
  exact primitive_root_exists_of_closure_bridge prime bridge

theorem additive_zmod_cyclic_exists_for_prime {p : BHist}
    (prime : NatPrime p) :
    ∃ g : ZMod p,
      ZModGenerates prime.left (NatPrime_empty_absurd prime) g := by
  exact zmod_cyclic_exists prime.left (NatPrime_empty_absurd prime)

end BEDC.Derived.PrimitiveRootCyclic
