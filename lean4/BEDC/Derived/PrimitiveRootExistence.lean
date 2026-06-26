import BEDC.Derived.PrimitiveRootUp

namespace BEDC.Derived.PrimitiveRootExistence

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.ZModUp
open BEDC.Derived.ZModFieldUp
open BEDC.Derived.ZModResidueList
open BEDC.Derived.PrimitiveRootUp

def PrimeUnitOrderLayer {p : BHist} (prime : NatPrime p)
    (k : BHist) (xs : List (ZMod p)) : Prop :=
  ListNoDup xs ∧
    (∀ x : ZMod p, x ∈ xs -> zmodNonzero x) ∧
      (∀ x : ZMod p, x ∈ xs ->
        HasMultOrder p prime.left (NatPrime_empty_absurd prime) x k)

theorem primeUnitOrderLayer_bound {p k : BHist} (prime : NatPrime p)
    {xs : List (ZMod p)} :
    PrimeUnitOrderLayer prime k xs ->
      0 < bwordLength k ->
        xs.length <= bwordLength k := by
  intro layer kPositive
  exact hasMultOrder_root_bound_list prime kPositive
    layer.left layer.right.right

private theorem unary_nonempty_length_positive {h : BHist} :
    UnaryHistory h -> (hsame h BHist.Empty -> False) ->
      0 < bwordLength h := by
  intro hUnary hNonempty
  cases h with
  | Empty =>
      exact False.elim (hNonempty rfl)
  | e0 _ =>
      cases hUnary
  | e1 tail =>
      change 0 < Nat.succ (bwordLength tail)
      exact Nat.succ_pos (bwordLength tail)

theorem unaryPred_length {p : BHist} :
    UnaryHistory p -> bwordLength (unaryPred p) = bwordLength p - 1 := by
  intro pUnary
  cases p with
  | Empty =>
      rfl
  | e0 _ =>
      cases pUnary
  | e1 _ =>
      rfl

theorem prime_unaryPred_positive {p : BHist} (prime : NatPrime p) :
    0 < bwordLength (unaryPred p) := by
  cases p with
  | Empty =>
      exact False.elim (NatPrime_empty_absurd prime rfl)
  | e0 _ =>
      cases prime.left
  | e1 tail =>
      exact unary_nonempty_length_positive
        (unary_e1_inversion prime.left)
        (fun tailEmpty => by
          cases tailEmpty
          exact NatPrime_unit_absurd prime)

theorem topOrderLayer_bound {p : BHist} (prime : NatPrime p)
    {xs : List (ZMod p)} :
    PrimeUnitOrderLayer prime (unaryPred p) xs ->
      xs.length <= bwordLength p - 1 := by
  intro layer
  have bound :
      xs.length <= bwordLength (unaryPred p) :=
    primeUnitOrderLayer_bound prime layer
      (prime_unaryPred_positive prime)
  rw [unaryPred_length prime.left] at bound
  exact bound

structure TopOrderWitness {p : BHist} (prime : NatPrime p) where
  generator : ZMod p
  generator_nonzero : zmodNonzero generator
  order :
    HasMultOrder p prime.left (NatPrime_empty_absurd prime)
      generator (unaryPred p)

theorem primitive_root_exists_of_top_order_witness {p : BHist}
    (prime : NatPrime p) :
    TopOrderWitness prime ->
      ∃ g : ZMod p,
        zmodNonzero g ∧
          IsPrimitiveRoot p prime.left (NatPrime_empty_absurd prime)
            (unaryPred p) g := by
  intro witness
  exact ⟨witness.generator, witness.generator_nonzero, witness.order⟩

theorem primitive_root_exists_of_top_order_layer {p : BHist}
    (prime : NatPrime p) {xs : List (ZMod p)} :
    PrimeUnitOrderLayer prime (unaryPred p) xs ->
      (∃ g : ZMod p, g ∈ xs) ->
        ∃ g : ZMod p,
          zmodNonzero g ∧
            IsPrimitiveRoot p prime.left (NatPrime_empty_absurd prime)
              (unaryPred p) g := by
  intro layer nonempty
  cases nonempty with
  | intro g gMem =>
      exact ⟨g, layer.right.left g gMem, layer.right.right g gMem⟩

theorem orderOf_eq_prime_minus_one_has_order {p : BHist}
    (prime : NatPrime p) (x : ZMod p) :
    orderOf prime x = unaryPred p ->
      HasMultOrder p prime.left (NatPrime_empty_absurd prime) x
        (unaryPred p) := by
  intro same
  unfold orderOf at same
  cases found :
      multOrderSearchFrom p prime.left (NatPrime_empty_absurd prime) x
        1 (nonzeroResidues prime).length with
  | none =>
      rw [found] at same
      have positive := prime_unaryPred_positive prime
      rw [← same] at positive
      exact False.elim (Nat.not_lt_zero 0 positive)
  | some k =>
      rw [found] at same
      have order :=
        multOrderSearchFrom_has_order p prime.left
          (NatPrime_empty_absurd prime) x found
      rw [← same]
      exact order

def bhistEqBool (x y : BHist) : Bool :=
  if x = y then true else false

theorem bhistEqBool_true {x y : BHist} :
    bhistEqBool x y = true -> x = y := by
  intro hit
  unfold bhistEqBool at hit
  by_cases same : x = y
  · exact same
  · rw [if_neg same] at hit
    cases hit

def primitiveRootSearchFrom {p : BHist} (prime : NatPrime p) :
    List (ZMod p) -> Option (ZMod p)
  | [] => none
  | x :: xs =>
      if bhistEqBool (orderOf prime x) (unaryPred p) then
        some x
      else
        primitiveRootSearchFrom prime xs

def primitiveRootSearch {p : BHist} (prime : NatPrime p) :
    Option (ZMod p) :=
  primitiveRootSearchFrom prime (nonzeroResidues prime)

theorem primitiveRootSearchFrom_mem {p : BHist} (prime : NatPrime p)
    {xs : List (ZMod p)} {g : ZMod p} :
    primitiveRootSearchFrom prime xs = some g -> g ∈ xs := by
  intro found
  induction xs with
  | nil =>
      cases found
  | cons x xs ih =>
      change
        (if bhistEqBool (orderOf prime x) (unaryPred p) then
          some x
        else
          primitiveRootSearchFrom prime xs) = some g at found
      cases hit : bhistEqBool (orderOf prime x) (unaryPred p) with
      | false =>
          rw [hit] at found
          exact List.Mem.tail x (ih found)
      | true =>
          rw [hit] at found
          cases found
          exact List.Mem.head xs

theorem primitiveRootSearch_mem {p : BHist} (prime : NatPrime p)
    {g : ZMod p} :
    primitiveRootSearch prime = some g -> g ∈ nonzeroResidues prime := by
  intro found
  exact primitiveRootSearchFrom_mem prime found

theorem primitiveRootSearch_nonzero {p : BHist} (prime : NatPrime p)
    {g : ZMod p} :
    primitiveRootSearch prime = some g -> zmodNonzero g := by
  intro found
  exact nonzeroResidues_all_nonzero prime g
    (primitiveRootSearch_mem prime found)

theorem primitiveRootSearchFrom_order {p : BHist} (prime : NatPrime p)
    {xs : List (ZMod p)} {g : ZMod p} :
    primitiveRootSearchFrom prime xs = some g ->
      HasMultOrder p prime.left (NatPrime_empty_absurd prime) g
        (unaryPred p) := by
  intro found
  induction xs with
  | nil =>
      cases found
  | cons x xs ih =>
      change
        (if bhistEqBool (orderOf prime x) (unaryPred p) then
          some x
        else
          primitiveRootSearchFrom prime xs) = some g at found
      cases hit : bhistEqBool (orderOf prime x) (unaryPred p) with
      | false =>
          rw [hit] at found
          exact ih found
      | true =>
          rw [hit] at found
          let head := x
          cases found
          exact orderOf_eq_prime_minus_one_has_order prime head
            (bhistEqBool_true hit)

theorem primitiveRootSearch_order {p : BHist} (prime : NatPrime p)
    {g : ZMod p} :
    primitiveRootSearch prime = some g ->
      HasMultOrder p prime.left (NatPrime_empty_absurd prime) g
        (unaryPred p) := by
  intro found
  exact primitiveRootSearchFrom_order prime found

structure PrimitiveRootSearchCertificate {p : BHist} (prime : NatPrime p) where
  result : ZMod p
  found : primitiveRootSearch prime = some result

def PrimitiveRootSearchCertificate.toTopOrderWitness {p : BHist}
    {prime : NatPrime p} (cert : PrimitiveRootSearchCertificate prime) :
    TopOrderWitness prime where
  generator := cert.result
  generator_nonzero := primitiveRootSearch_nonzero prime cert.found
  order := primitiveRootSearch_order prime cert.found

theorem primitive_root_exists_of_search_certificate {p : BHist}
    (prime : NatPrime p) :
    PrimitiveRootSearchCertificate prime ->
      ∃ g : ZMod p,
        zmodNonzero g ∧
          IsPrimitiveRoot p prime.left (NatPrime_empty_absurd prime)
            (unaryPred p) g := by
  intro cert
  exact primitive_root_exists_of_top_order_witness prime cert.toTopOrderWitness

theorem primitive_root_order_divides_prime_minus_one {p phi : BHist}
    (prime : NatPrime p) {g : ZMod p} :
    zmodNonzero g ->
      IsPrimitiveRoot p prime.left (NatPrime_empty_absurd prime) phi g ->
        NatDivides phi (unaryPred p) := by
  intro gNonzero primitive
  exact hasMultOrder_divides_prime_minus_one prime g gNonzero primitive

end BEDC.Derived.PrimitiveRootExistence
