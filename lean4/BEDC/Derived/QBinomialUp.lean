import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.NarayanaUp

namespace BEDC.Derived.QBinomialUp

abbrev Poly : Type :=
  List Nat

def polyZero : Poly :=
  []

def polyOne : Poly :=
  [0]

def polyAdd : Poly -> Poly -> Poly
  | [], q => q
  | e :: p, q => e :: polyAdd p q

def qShift (m : Nat) (p : Poly) : Poly :=
  p.map (fun e => m + e)

def polyCoeff (target : Nat) : Poly -> Nat
  | [] => 0
  | e :: p =>
      if e = target then Nat.succ (polyCoeff target p) else polyCoeff target p

def polyEvalOne : Poly -> Nat
  | [] => 0
  | _ :: p => Nat.succ (polyEvalOne p)

def qNat : Nat -> Poly
  | 0 => polyZero
  | Nat.succ n => polyAdd polyOne (qShift 1 (qNat n))

def polyMul (p q : Poly) : Poly :=
  p.foldr (fun e acc => polyAdd (qShift e q) acc) polyZero

def qFactorial : Nat -> Poly
  | 0 => polyOne
  | Nat.succ n => polyMul (qFactorial n) (qNat (Nat.succ n))

def qBinomial : Nat -> Nat -> Poly
  | 0, 0 => polyOne
  | 0, Nat.succ _ => polyZero
  | Nat.succ _, 0 => polyOne
  | Nat.succ n, Nat.succ k =>
      polyAdd (qBinomial n k) (qShift (Nat.succ k) (qBinomial n (Nat.succ k)))

def qGaussian (k l : Nat) : Poly :=
  qBinomial (k + l) k

def polyEq (p q : Poly) : Prop :=
  forall target : Nat, polyCoeff target p = polyCoeff target q

theorem polyCoeff_append :
    forall p q : Poly, forall target : Nat,
      polyCoeff target (polyAdd p q) = polyCoeff target p + polyCoeff target q
  | [], q, target => by
      exact (Nat.zero_add (polyCoeff target q)).symm
  | e :: p, q, target => by
      change
        (if e = target then Nat.succ (polyCoeff target (polyAdd p q))
          else polyCoeff target (polyAdd p q)) =
          (if e = target then Nat.succ (polyCoeff target p)
            else polyCoeff target p) + polyCoeff target q
      rw [polyCoeff_append p q target]
      by_cases h : e = target
      · rw [if_pos h, if_pos h]
        exact (Nat.succ_add (polyCoeff target p) (polyCoeff target q)).symm
      · rw [if_neg h, if_neg h]

theorem polyCoeff_add_comm (p q : Poly) :
    polyEq (polyAdd p q) (polyAdd q p) := by
  intro target
  rw [polyCoeff_append p q target]
  rw [polyCoeff_append q p target]
  exact Nat.add_comm (polyCoeff target p) (polyCoeff target q)

theorem polyCoeff_shift_zero :
    forall p : Poly, polyEq (qShift 0 p) p
  | [] => by
      intro target
      rfl
  | e :: p => by
      intro target
      change
        (if 0 + e = target then Nat.succ (polyCoeff target (qShift 0 p))
          else polyCoeff target (qShift 0 p)) =
          (if e = target then Nat.succ (polyCoeff target p) else polyCoeff target p)
      rw [Nat.zero_add]
      have ih := polyCoeff_shift_zero p target
      rw [ih]

theorem polyEvalOne_append :
    forall p q : Poly,
      polyEvalOne (polyAdd p q) = polyEvalOne p + polyEvalOne q
  | [], q => by
      exact (Nat.zero_add (polyEvalOne q)).symm
  | _ :: p, q => by
      change Nat.succ (polyEvalOne (polyAdd p q)) =
        Nat.succ (polyEvalOne p) + polyEvalOne q
      rw [polyEvalOne_append p q]
      exact (Nat.succ_add (polyEvalOne p) (polyEvalOne q)).symm

theorem polyEvalOne_qShift :
    forall m : Nat, forall p : Poly, polyEvalOne (qShift m p) = polyEvalOne p
  | _m, [] => rfl
  | m, _ :: p => by
      change Nat.succ (polyEvalOne (qShift m p)) = Nat.succ (polyEvalOne p)
      rw [polyEvalOne_qShift m p]

theorem qBinomial_pascal (n k : Nat) :
    qBinomial (Nat.succ n) (Nat.succ k) =
      polyAdd (qBinomial n k) (qShift (Nat.succ k) (qBinomial n (Nat.succ k))) := by
  rfl

theorem qBinomial_zero_right (n : Nat) :
    qBinomial n 0 = polyOne := by
  cases n <;> rfl

theorem qBinomial_zero_left_succ (k : Nat) :
    qBinomial 0 (Nat.succ k) = polyZero := by
  rfl

theorem qBinomial_above :
    forall n extra : Nat,
      qBinomial n (Nat.succ (n + extra)) = polyZero
  | 0, extra => by
      rfl
  | Nat.succ n, extra => by
      rw [Nat.succ_add]
      change
        polyAdd (qBinomial n (Nat.succ (n + extra)))
          (qShift (Nat.succ (Nat.succ (n + extra)))
            (qBinomial n (Nat.succ (Nat.succ (n + extra))))) = polyZero
      rw [qBinomial_above n extra]
      have shifted : n + Nat.succ extra = Nat.succ (n + extra) := Nat.add_succ n extra
      rw [← shifted]
      rw [qBinomial_above n (Nat.succ extra)]
      rfl

theorem qBinomial_self :
    forall n : Nat, qBinomial n n = polyOne
  | 0 => rfl
  | Nat.succ n => by
      change
        polyAdd (qBinomial n n)
          (qShift (Nat.succ n) (qBinomial n (Nat.succ n))) = polyOne
      rw [qBinomial_self n]
      have above : qBinomial n (Nat.succ (n + 0)) = polyZero :=
        qBinomial_above n 0
      rw [Nat.add_zero] at above
      rw [above]
      rfl

theorem qGaussian_pascal (k l : Nat) :
    qGaussian (Nat.succ k) (Nat.succ l) =
      polyAdd (qGaussian k (Nat.succ l))
        (qShift (Nat.succ k) (qGaussian (Nat.succ k) l)) := by
  unfold qGaussian
  rw [Nat.succ_add]
  rw [Nat.add_succ]
  rw [Nat.succ_add k l]
  have step := qBinomial_pascal (Nat.succ (k + l)) k
  exact step

theorem qGaussian_zero_left :
    forall l : Nat, qGaussian 0 l = polyOne
  | l => by
      unfold qGaussian
      rw [Nat.zero_add]
      exact qBinomial_zero_right l

theorem qGaussian_zero_right :
    forall k : Nat, qGaussian k 0 = polyOne
  | k => by
      unfold qGaussian
      rw [Nat.add_zero]
      exact qBinomial_self k

theorem qBinomial_evalOne (n k : Nat) :
    polyEvalOne (qBinomial n k) = BEDC.Derived.BinomialIdentitiesUp.C n k := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => rfl
      | succ k =>
          change 0 = BEDC.Derived.BinomialIdentitiesUp.C 0 (Nat.succ k)
          exact (BEDC.Derived.BinomialIdentitiesUp.binomial_zero_left_succ k).symm
  | succ n ih =>
      cases k with
      | zero =>
          change 1 = BEDC.Derived.BinomialIdentitiesUp.C (Nat.succ n) 0
          exact (BEDC.Derived.BinomialIdentitiesUp.binomial_zero_right (Nat.succ n)).symm
      | succ k =>
          rw [qBinomial_pascal n k]
          rw [polyEvalOne_append]
          rw [polyEvalOne_qShift]
          rw [ih k]
          rw [ih (Nat.succ k)]
          exact (BEDC.Derived.BinomialIdentitiesUp.binomial_pascal n k).symm

theorem qBinomial_from_qGaussian :
    forall k l : Nat, qBinomial (k + l) k = qGaussian k l
  | k, l => by
      rfl

theorem qBinomial_evalOne_complement (k l : Nat) :
    polyEvalOne (qBinomial (k + l) k) =
      BEDC.Derived.BinomialIdentitiesUp.C (k + l) l := by
  rw [qBinomial_evalOne]
  exact BEDC.Derived.NarayanaUp.binomial_complement_symmetry k l

theorem qBinomial_constructive_export :
    (forall n k : Nat,
      qBinomial (Nat.succ n) (Nat.succ k) =
        polyAdd (qBinomial n k)
          (qShift (Nat.succ k) (qBinomial n (Nat.succ k)))) ∧
      (forall n k : Nat,
        polyEvalOne (qBinomial n k) =
          BEDC.Derived.BinomialIdentitiesUp.C n k) ∧
      (forall k l : Nat,
        qBinomial (k + l) k = qGaussian k l) ∧
      (forall k l : Nat,
        polyEvalOne (qBinomial (k + l) k) =
          BEDC.Derived.BinomialIdentitiesUp.C (k + l) l) := by
  constructor
  · exact qBinomial_pascal
  · constructor
    · exact qBinomial_evalOne
    · constructor
      · exact qBinomial_from_qGaussian
      · exact qBinomial_evalOne_complement

end BEDC.Derived.QBinomialUp
