import BEDC.Derived.Window6FibonacciCount

namespace BEDC.Derived.Window6Transfer

abbrev fib : Nat -> Nat :=
  BEDC.Derived.Window6Fibonacci.fib

/--
The matrix `M = [[1, 1], [1, 0]]` is the Window6 stable-word transfer
matrix.  The Python count route gives `|X_m| = F_{m+2}` and the Perron
spectral root `phi`; this Lean file records the algebraic root data:
characteristic polynomial `x^2 - x - 1`, the Fibonacci power identity,
and the Cassini determinant identity, all by first-principles recursion.
-/
structure Mat2 where
  a : Int
  b : Int
  c : Int
  d : Int
deriving DecidableEq

def mul (X Y : Mat2) : Mat2 :=
  ⟨X.a * Y.a + X.b * Y.c,
    X.a * Y.b + X.b * Y.d,
    X.c * Y.a + X.d * Y.c,
    X.c * Y.b + X.d * Y.d⟩

def I : Mat2 :=
  ⟨1, 0, 0, 1⟩

def M : Mat2 :=
  ⟨1, 1, 1, 0⟩

def npow (X : Mat2) : Nat -> Mat2
  | 0 => I
  | n + 1 => mul (npow X n) X

def trace (X : Mat2) : Int :=
  X.a + X.d

def det (X : Mat2) : Int :=
  X.a * X.d - X.b * X.c

theorem M_trace_det : trace M = 1 ∧ det M = -1 := by
  constructor
  · rfl
  · rfl

private theorem mat2_eq {X Y : Mat2}
    (ha : X.a = Y.a) (hb : X.b = Y.b)
    (hc : X.c = Y.c) (hd : X.d = Y.d) : X = Y := by
  cases X with
  | mk a b c d =>
      cases Y with
      | mk a' b' c' d' =>
          cases ha
          cases hb
          cases hc
          cases hd
          rfl

private theorem natCast_mul_one (a : Nat) :
    ((a : Nat) : Int) * (1 : Int) = ((a : Nat) : Int) := by
  change ((a * 1 : Nat) : Int) = ((a : Nat) : Int)
  rw [Nat.mul_one]

private theorem natCast_mul_zero (a : Nat) :
    ((a : Nat) : Int) * (0 : Int) = ((0 : Nat) : Int) := by
  change ((a * 0 : Nat) : Int) = ((0 : Nat) : Int)
  rw [Nat.mul_zero]

private theorem add_mul_pure (a b c : Nat) :
    (a + b) * c = a * c + b * c := by
  induction c with
  | zero =>
      rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | succ c ih =>
      calc
        (a + b) * Nat.succ c =
            (a + b) * c + (a + b) := Nat.mul_succ (a + b) c
        _ = (a * c + b * c) + (a + b) :=
          congrArg (fun x => x + (a + b)) ih
        _ = a * c + (b * c + (a + b)) :=
          Nat.add_assoc (a * c) (b * c) (a + b)
        _ = a * c + ((b * c + a) + b) :=
          congrArg (fun x => a * c + x) (Nat.add_assoc (b * c) a b).symm
        _ = a * c + ((a + b * c) + b) :=
          congrArg (fun x => a * c + (x + b)) (Nat.add_comm (b * c) a)
        _ = a * c + (a + (b * c + b)) :=
          congrArg (fun x => a * c + x) (Nat.add_assoc a (b * c) b)
        _ = (a * c + a) + (b * c + b) :=
          (Nat.add_assoc (a * c) a (b * c + b)).symm
        _ = a * Nat.succ c + (b * c + b) :=
          congrArg (fun x => x + (b * c + b)) (Nat.mul_succ a c).symm
        _ = a * Nat.succ c + b * Nat.succ c :=
          congrArg (fun x => a * Nat.succ c + x) (Nat.mul_succ b c).symm

private theorem mul_fib_pair_M (n : Nat) :
    mul (⟨((fib (n + 2) : Nat) : Int), ((fib (n + 1) : Nat) : Int),
          ((fib (n + 1) : Nat) : Int), ((fib n : Nat) : Int)⟩) M =
      ⟨((fib (n + 3) : Nat) : Int), ((fib (n + 2) : Nat) : Int),
        ((fib (n + 2) : Nat) : Int), ((fib (n + 1) : Nat) : Int)⟩ := by
  apply mat2_eq
  · change ((fib (n + 2) : Nat) : Int) * (1 : Int) +
      ((fib (n + 1) : Nat) : Int) * (1 : Int) =
      ((fib (n + 3) : Nat) : Int)
    rw [natCast_mul_one, natCast_mul_one]
    rfl
  · change ((fib (n + 2) : Nat) : Int) * (1 : Int) +
      ((fib (n + 1) : Nat) : Int) * (0 : Int) =
      ((fib (n + 2) : Nat) : Int)
    rw [natCast_mul_one, natCast_mul_zero]
    rfl
  · change ((fib (n + 1) : Nat) : Int) * (1 : Int) +
      ((fib n : Nat) : Int) * (1 : Int) =
      ((fib (n + 2) : Nat) : Int)
    rw [natCast_mul_one, natCast_mul_one]
    rfl
  · change ((fib (n + 1) : Nat) : Int) * (1 : Int) +
      ((fib n : Nat) : Int) * (0 : Int) =
      ((fib (n + 1) : Nat) : Int)
    rw [natCast_mul_one, natCast_mul_zero]
    rfl

theorem M_pow_fib (n : Nat) :
    npow M (n + 1) =
      ⟨((fib (n + 2) : Nat) : Int),
        ((fib (n + 1) : Nat) : Int),
        ((fib (n + 1) : Nat) : Int),
        ((fib n : Nat) : Int)⟩ := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [npow, ih, mul_fib_pair_M]

def altSign : Nat -> Int
  | 0 => 1
  | n + 1 => -altSign n

private theorem int_neg_neg (x : Int) :
    -(-x) = x := by
  cases x with
  | ofNat n =>
      cases n with
      | zero => rfl
      | succ n => rfl
  | negSucc n => rfl

private theorem altSign_two_step (n : Nat) :
    altSign (n + 2) = altSign n := by
  rw [show altSign (n + 2) = -(-altSign n) by rfl]
  rw [int_neg_neg]

private def cassiniPos (n : Nat) : Prop :=
  fib (n + 2) * fib n + 1 = fib (n + 1) * fib (n + 1)

private def cassiniNeg (n : Nat) : Prop :=
  fib (n + 2) * fib n = fib (n + 1) * fib (n + 1) + 1

private theorem cassiniPos_to_neg_succ (n : Nat)
    (ih : cassiniPos n) :
    cassiniNeg (n + 1) := by
  unfold cassiniPos at ih
  unfold cassiniNeg
  calc
    fib (n + 1 + 2) * fib (n + 1) =
        fib (n + 3) * fib (n + 1) := rfl
    _ = (fib (n + 2) + fib (n + 1)) * fib (n + 1) := rfl
    _ = fib (n + 2) * fib (n + 1) + fib (n + 1) * fib (n + 1) :=
      add_mul_pure _ _ _
    _ = fib (n + 2) * fib (n + 1) + (fib (n + 2) * fib n + 1) :=
      congrArg (fun x => fib (n + 2) * fib (n + 1) + x) ih.symm
    _ = (fib (n + 2) * fib (n + 1) + fib (n + 2) * fib n) + 1 :=
      (Nat.add_assoc _ _ _).symm
    _ = fib (n + 2) * (fib (n + 1) + fib n) + 1 :=
      congrArg (fun x => x + 1)
        (Nat.mul_add (fib (n + 2)) (fib (n + 1)) (fib n)).symm
    _ = fib (n + 2) * fib (n + 2) + 1 := rfl
    _ = fib (n + 1 + 1) * fib (n + 1 + 1) + 1 := rfl

private theorem cassiniNeg_to_pos_succ (n : Nat)
    (ih : cassiniNeg n) :
    cassiniPos (n + 1) := by
  unfold cassiniNeg at ih
  unfold cassiniPos
  calc
    fib (n + 1 + 2) * fib (n + 1) + 1 =
        fib (n + 3) * fib (n + 1) + 1 := rfl
    _ = (fib (n + 2) + fib (n + 1)) * fib (n + 1) + 1 := rfl
    _ = (fib (n + 2) * fib (n + 1) + fib (n + 1) * fib (n + 1)) + 1 :=
      congrArg (fun x => x + 1) (add_mul_pure _ _ _)
    _ = fib (n + 2) * fib (n + 1) + (fib (n + 1) * fib (n + 1) + 1) :=
      Nat.add_assoc _ _ _
    _ = fib (n + 2) * fib (n + 1) + fib (n + 2) * fib n :=
      congrArg (fun x => fib (n + 2) * fib (n + 1) + x) ih.symm
    _ = fib (n + 2) * (fib (n + 1) + fib n) :=
      (Nat.mul_add (fib (n + 2)) (fib (n + 1)) (fib n)).symm
    _ = fib (n + 2) * fib (n + 2) := rfl
    _ = fib (n + 1 + 1) * fib (n + 1 + 1) := rfl

private theorem cassiniPos_even (n : Nat) :
    cassiniPos (2 * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change cassiniPos (2 * n + 2)
      rw [show 2 * n + 2 = (2 * n + 1) + 1 by rfl]
      exact cassiniNeg_to_pos_succ (2 * n + 1)
        (cassiniPos_to_neg_succ (2 * n) ih)

private theorem cassiniNeg_odd (n : Nat) :
    cassiniNeg (2 * n + 1) :=
  cassiniPos_to_neg_succ (2 * n) (cassiniPos_even n)

private theorem sub_self_succ (a : Nat) :
    a - (a + 1) = 0 := by
  induction a with
  | zero => rfl
  | succ a ih =>
      change Nat.succ a - Nat.succ (a + 1) = 0
      rw [Nat.succ_sub_succ_eq_sub, ih]

private theorem succ_sub_self (a : Nat) :
    (a + 1) - a = 1 := by
  induction a with
  | zero => rfl
  | succ a ih =>
      change Nat.succ (a + 1) - Nat.succ a = 1
      rw [Nat.succ_sub_succ_eq_sub, ih]

private theorem subNatNat_succ_left (a : Nat) :
    Int.subNatNat (a + 1) a = 1 := by
  unfold Int.subNatNat
  rw [sub_self_succ]
  rw [succ_sub_self]
  rfl

private theorem subNatNat_succ_right (a : Nat) :
    Int.subNatNat a (a + 1) = -1 := by
  unfold Int.subNatNat
  rw [succ_sub_self]
  rfl

private theorem cast_sub_of_add_one_eq (a b : Nat) (h : a + 1 = b) :
    (((a : Nat) : Int) - ((b : Nat) : Int)) = -1 := by
  cases h
  cases a with
  | zero => rfl
  | succ a =>
      change Int.subNatNat (a + 1) (a + 2) = -1
      exact subNatNat_succ_right (a + 1)

private theorem cast_sub_of_eq_add_one (a b : Nat) (h : a = b + 1) :
    (((a : Nat) : Int) - ((b : Nat) : Int)) = 1 := by
  cases h
  cases b with
  | zero => rfl
  | succ b =>
      change Int.subNatNat (b + 2) (b + 1) = 1
      exact subNatNat_succ_left (b + 1)

private theorem det_even_fib_pair (n : Nat) :
    det (⟨((fib (2 * n + 2) : Nat) : Int),
      ((fib (2 * n + 1) : Nat) : Int),
      ((fib (2 * n + 1) : Nat) : Int),
      ((fib (2 * n) : Nat) : Int)⟩) = -1 := by
  unfold det
  change (((fib (2 * n + 2) * fib (2 * n) : Nat) : Int) -
    ((fib (2 * n + 1) * fib (2 * n + 1) : Nat) : Int)) = -1
  exact cast_sub_of_add_one_eq
    (fib (2 * n + 2) * fib (2 * n))
    (fib (2 * n + 1) * fib (2 * n + 1))
    (cassiniPos_even n)

private theorem det_odd_fib_pair (n : Nat) :
    det (⟨((fib (2 * n + 3) : Nat) : Int),
      ((fib (2 * n + 2) : Nat) : Int),
      ((fib (2 * n + 2) : Nat) : Int),
      ((fib (2 * n + 1) : Nat) : Int)⟩) = 1 := by
  unfold det
  change (((fib (2 * n + 3) * fib (2 * n + 1) : Nat) : Int) -
    ((fib (2 * n + 2) * fib (2 * n + 2) : Nat) : Int)) = 1
  exact cast_sub_of_eq_add_one
    (fib (2 * n + 3) * fib (2 * n + 1))
    (fib (2 * n + 2) * fib (2 * n + 2))
    (cassiniNeg_odd n)

private inductive Parity : Nat -> Type where
  | even (k : Nat) : Parity (2 * k)
  | odd (k : Nat) : Parity (2 * k + 1)

private def parity : (n : Nat) -> Parity n
  | 0 => Parity.even 0
  | 1 => Parity.odd 0
  | n + 2 =>
      match parity n with
      | Parity.even k => by
          change Parity (2 * (k + 1))
          exact Parity.even (k + 1)
      | Parity.odd k => by
          change Parity (2 * (k + 1) + 1)
          exact Parity.odd (k + 1)

theorem cassini (n : Nat) :
    det (npow M n) = altSign n := by
  cases parity n with
  | even k =>
      cases k with
      | zero => rfl
      | succ k =>
          rw [show 2 * Nat.succ k = (2 * k + 1) + 1 by rfl]
          rw [M_pow_fib]
          change det (⟨((fib (2 * k + 3) : Nat) : Int),
            ((fib (2 * k + 2) : Nat) : Int),
            ((fib (2 * k + 2) : Nat) : Int),
            ((fib (2 * k + 1) : Nat) : Int)⟩) = altSign (2 * k + 1 + 1)
          rw [det_odd_fib_pair]
          rw [show altSign (2 * k + 1 + 1) = 1 by
            induction k with
            | zero => rfl
            | succ k ih =>
                change altSign (2 * k + 1 + 1 + 2) = 1
                rw [altSign_two_step]
                exact ih]
  | odd k =>
      rw [show 2 * k + 1 = (2 * k) + 1 by rfl]
      rw [M_pow_fib]
      change det (⟨((fib (2 * k + 2) : Nat) : Int),
        ((fib (2 * k + 1) : Nat) : Int),
        ((fib (2 * k + 1) : Nat) : Int),
        ((fib (2 * k) : Nat) : Int)⟩) = altSign (2 * k + 1)
      rw [det_even_fib_pair]
      rw [show altSign (2 * k + 1) = -1 by
        induction k with
        | zero => rfl
        | succ k ih =>
            change altSign (2 * k + 1 + 2) = -1
            rw [altSign_two_step]
            exact ih]

theorem M_pow_six :
    npow M 6 = ⟨((fib 7 : Nat) : Int), ((fib 6 : Nat) : Int),
      ((fib 6 : Nat) : Int), ((fib 5 : Nat) : Int)⟩ := by
  exact M_pow_fib 5

theorem M_pow_six_values :
    npow M 6 = ⟨13, 8, 8, 5⟩ := by
  rfl

theorem det_M_pow_six :
    det (npow M 6) = 1 := by
  rfl

theorem det_M_pow_six_eq_neg_one_pow :
    det (npow M 6) = (-1 : Int) ^ 6 := by
  rfl

end BEDC.Derived.Window6Transfer
