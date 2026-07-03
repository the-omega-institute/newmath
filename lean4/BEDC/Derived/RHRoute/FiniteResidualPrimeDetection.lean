import BEDC.Real.RatNumKernel

namespace BEDC.Derived.RHRoute.FiniteResidualPrimeDetection

open BEDC.Derived.RationalUp
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.FKernel.Cont
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PadicUp
open BEDC.Real.RatNumKernel

abbrev Rat : Type :=
  RatNum

/-!
Finite residue-class detection kernel (evaluation form) of the
prime-generated sieve (Theorem 7.1).

This is not the character/frequency version and not RH.  The modulus `m` is an
explicit hypothesis; resolving infinitely many frequencies would require
unbounded moduli, i.e. infinitude of primes.
-/

def classSum : List (Nat × Rat) -> Nat -> Nat -> Rat
  | [], _m, _a => ratZero
  | (s, c) :: t, m, a =>
      if s % m = a then ratAdd c (classSum t m a) else classSum t m a

theorem classSum_absent (l : List (Nat × Rat)) (m a : Nat)
    (h : ∀ p ∈ l, p.1 % m ≠ a) :
    RatEq (classSum l m a) ratZero := by
  induction l with
  | nil =>
      exact RatEq_refl ratZero
  | cons p t ih =>
      unfold classSum
      have headAbsent : p.1 % m ≠ a := by
        exact h p (List.Mem.head t)
      rw [if_neg headAbsent]
      exact ih (by
        intro q qmem
        exact h q (List.Mem.tail p qmem))

theorem head_detection (s : Nat) (c : Rat) (rest : List (Nat × Rat)) (m : Nat)
    (hsep : ∀ p ∈ rest, p.1 % m ≠ s % m) :
    RatEq (classSum ((s, c) :: rest) m (s % m)) c := by
  unfold classSum
  rw [if_pos rfl]
  exact RatEq_trans _ _ _
    (ratAdd_respects (RatEq_refl c)
      (classSum_absent rest m (s % m) hsep))
    (ratAdd_zero_right c)

private theorem natOne_strict_of_tail (tail : BHist) :
    UnaryHistory tail -> (tail = BHist.Empty -> False) ->
      NatUnaryStrictPrefix NatOne (BHist.e1 tail) := by
  intro tailUnary tailNonempty
  have shifted : append NatOne tail = BHist.e1 tail :=
    (unary_append_e1_left (h := tail) (k := BHist.Empty) tailUnary).trans
      (congrArg BHist.e1 (append_empty_left tail))
  exact ⟨tail, tailUnary, tailNonempty, cont_intro shifted.symm⟩

private theorem intEq_zero_of_magnitude_empty {x : BEDC.Derived.PrimeUp.IntegerUp} :
    hsame x.magnitude BHist.Empty -> IntEq x intZero := by
  intro magEmpty
  cases x with
  | mk sign magnitude carrier =>
      cases sign with
      | b0 =>
          unfold IntEq intZero intOfNat intToPair
          apply IntPairClassifier_of_length_eq
          · exact ⟨carrier.right, unary_empty⟩
          · exact ⟨unary_empty, unary_empty⟩
          change
            bwordLength magnitude + bwordLength BHist.Empty =
              bwordLength BHist.Empty + bwordLength BHist.Empty
          rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left]
          rw [Nat.add_zero, Nat.zero_add]
          exact congrArg bwordLength magEmpty
      | b1 =>
          unfold IntEq intZero intOfNat intToPair
          apply IntPairClassifier_of_length_eq
          · exact ⟨unary_empty, carrier.right⟩
          · exact ⟨unary_empty, unary_empty⟩
          change
            bwordLength BHist.Empty + bwordLength BHist.Empty =
              bwordLength BHist.Empty + bwordLength magnitude
          rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left]
          rw [Nat.zero_add, Nat.zero_add]
          exact (congrArg bwordLength magEmpty).symm

private theorem ratEq_zero_of_num_intEq {x : Rat} :
    IntEq x.num intZero -> RatEq x ratZero := by
  intro numZero
  unfold RatEq
  change
    IntEq (IntMul x.num (ratDenInt ratZero))
      (IntMul ratZero.num (ratDenInt x))
  have leftToZero :
      IntEq (IntMul x.num (ratDenInt ratZero)) intZero :=
    IntEq_trans (intMul_left_congr (c := x.num) ratDenInt_zero)
      (IntEq_trans (intMul_one_right x.num) numZero)
  have rightToZero :
      IntEq (IntMul ratZero.num (ratDenInt x)) intZero := by
    change IntEq (IntMul intZero (ratDenInt x)) intZero
    exact intMul_zero_left (ratDenInt x)
  exact IntEq_trans leftToZero (IntEq_symm rightToZero)

private theorem ratApart0_of_RatEq_num {x y : Rat} :
    RatEq x y -> ratApart0 y -> ratApart0 x := by
  intro hxy hy
  cases x with
  | mk num den denPos =>
      cases num with
      | mk sign magnitude carrier =>
          cases magnitude with
          | Empty =>
              have xZero : RatEq
                  { num := { sign := sign, magnitude := BHist.Empty, carrier := carrier },
                    den := den, den_pos := denPos } ratZero :=
                ratEq_zero_of_num_intEq
                  (intEq_zero_of_magnitude_empty (hsame_refl BHist.Empty))
              have yZero : RatEq y ratZero :=
                RatEq_trans _ _ _ (RatEq_symm hxy) xZero
              exact False.elim
                (intApart0_not_zero_pair hy (RatEq_zero_num yZero))
          | e0 tail =>
              exact False.elim (unary_no_zero_extension carrier.right)
          | e1 tail =>
              cases tail with
              | Empty =>
                  exact Or.inr (hsame_refl NatOne)
              | e0 tail =>
                  exact False.elim (unary_no_zero_extension (unary_e1_inversion carrier.right))
              | e1 tail =>
                  exact Or.inl
                    (natOne_strict_of_tail (BHist.e1 tail)
                      (unary_e1_inversion carrier.right) (fun empty => by
                        exact not_hsame_e1_empty empty))

private theorem ratApart0_of_RatEq {x y : Rat} :
    RatEq x y -> ratApart0 y -> ratApart0 x := by
  exact ratApart0_of_RatEq_num

theorem head_detection_nonzero (s : Nat) (c : Rat)
    (rest : List (Nat × Rat)) (m : Nat)
    (hsep : ∀ p ∈ rest, p.1 % m ≠ s % m) (hc : ratApart0 c) :
    ratApart0 (classSum ((s, c) :: rest) m (s % m)) := by
  exact ratApart0_of_RatEq (head_detection s c rest m hsep) hc

end BEDC.Derived.RHRoute.FiniteResidualPrimeDetection
