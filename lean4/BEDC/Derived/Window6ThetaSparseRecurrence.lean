namespace BEDC.Derived.Window6ThetaSparseRecurrence

/-- Nonnegative four-state transfer. `c n = (a,b,e,f)`;
Fibonacci-cube theta-sparse vertex count is read out by `S m`. -/
def c : Nat → Nat × Nat × Nat × Nat
  | 0 => (1, 0, 0, 0)
  | n + 1 =>
      let a := (c n).1
      let b := (c n).2.1
      let e := (c n).2.2.1
      let f := (c n).2.2.2
      ((b + e) + f, a, b, e)

def S (m : Nat) : Nat :=
  ((c m).1 + 2 * (c m).2.1) + ((c m).2.2.1 + (c m).2.2.2)

theorem S_zero : S 0 = 1 := rfl
theorem S_one : S 1 = 2 := rfl
theorem S_two : S 2 = 2 := rfl
theorem S_three : S 3 = 4 := rfl
theorem S_four : S 4 = 5 := rfl
theorem S_five : S 5 = 8 := rfl

/-- Balanced four-term linear form. -/
def lin (a b e f p q r s : Nat) : Nat := (p * a + q * b) + (r * e + s * f)

/-- Exchange the middle summands using only associativity and right commutation. -/
theorem swap_mid (p q r s : Nat) : (p + q) + (r + s) = (p + r) + (q + s) := by
  rw [← Nat.add_assoc (p + q) r s, Nat.add_right_comm p q r, Nat.add_assoc (p + r) q s]

theorem add_mul_pure (p q a : Nat) : (p + q) * a = p * a + q * a := by
  induction a with
  | zero =>
      rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero, Nat.add_zero]
  | succ a ih =>
      rw [Nat.mul_add (p + q) a 1, Nat.mul_add p a 1, Nat.mul_add q a 1,
        Nat.mul_one, Nat.mul_one, Nat.mul_one, ih, swap_mid (p * a) (q * a) p q]

theorem mul_assoc_pure (p q a : Nat) : (p * q) * a = p * (q * a) := by
  induction a with
  | zero =>
      rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | succ a ih =>
      rw [Nat.mul_add (p * q) a 1, Nat.mul_one, Nat.mul_add q a 1,
        Nat.mul_one, Nat.mul_add p (q * a) q, ih]

/-- Addition of two linear forms over the same basis. -/
theorem lin_add (a b e f p q r s p' q' r' s' : Nat) :
    lin a b e f p q r s + lin a b e f p' q' r' s'
      = lin a b e f (p + p') (q + q') (r + r') (s + s') := by
  unfold lin
  rw [swap_mid (p * a + q * b) (r * e + s * f) (p' * a + q' * b) (r' * e + s' * f),
      swap_mid (p * a) (q * b) (p' * a) (q' * b),
      swap_mid (r * e) (s * f) (r' * e) (s' * f),
      ← add_mul_pure p p' a, ← add_mul_pure q q' b,
      ← add_mul_pure r r' e, ← add_mul_pure s s' f]

/-- Scalar multiplication by two distributes over the linear form. -/
theorem lin_two (a b e f p q r s : Nat) :
    2 * lin a b e f p q r s = lin a b e f (2 * p) (2 * q) (2 * r) (2 * s) := by
  unfold lin
  rw [Nat.mul_add 2 (p * a + q * b) (r * e + s * f),
      Nat.mul_add 2 (p * a) (q * b), Nat.mul_add 2 (r * e) (s * f),
      ← mul_assoc_pure 2 p a, ← mul_assoc_pure 2 q b,
      ← mul_assoc_pure 2 r e, ← mul_assoc_pure 2 s f]

theorem c_step_one (n : Nat) :
    (c (n + 1)).1 = (((c n).2.1 + (c n).2.2.1) + (c n).2.2.2) := rfl

theorem c_step_two (n : Nat) :
    (c (n + 1)).2.1 = (c n).1 := rfl

theorem c_step_three (n : Nat) :
    (c (n + 1)).2.2.1 = (c n).2.1 := rfl

theorem c_step_four (n : Nat) :
    (c (n + 1)).2.2.2 = (c n).2.2.1 := rfl

theorem c_one_one (n : Nat) :
    (c (n + 1)).1 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 0 1 1 1 := by
  rw [c_step_one n]
  unfold lin
  rw [Nat.zero_mul, Nat.one_mul, Nat.one_mul, Nat.one_mul, Nat.zero_add,
      Nat.add_assoc (c n).2.1 (c n).2.2.1 (c n).2.2.2]

theorem c_one_two (n : Nat) :
    (c (n + 1)).2.1 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 1 0 0 0 := by
  rw [c_step_two n]
  unfold lin
  rw [Nat.one_mul, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul, Nat.add_zero]

theorem c_one_three (n : Nat) :
    (c (n + 1)).2.2.1 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 0 1 0 0 := by
  rw [c_step_three n]
  unfold lin
  rw [Nat.zero_mul, Nat.one_mul, Nat.zero_mul, Nat.zero_mul, Nat.zero_add, Nat.add_zero]

theorem c_one_four (n : Nat) :
    (c (n + 1)).2.2.2 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 0 0 1 0 := by
  rw [c_step_four n]
  unfold lin
  rw [Nat.zero_mul, Nat.zero_mul, Nat.one_mul, Nat.zero_mul, Nat.zero_add, Nat.add_zero]

theorem c_two_one (n : Nat) :
    (c (n + 2)).1 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 1 1 1 0 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_one (n + 1), c_one_two n, c_one_three n, c_one_four n, lin_add, lin_add]

theorem c_two_two (n : Nat) :
    (c (n + 2)).2.1 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 0 1 1 1 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_two (n + 1), c_one_one n]

theorem c_two_three (n : Nat) :
    (c (n + 2)).2.2.1 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 1 0 0 0 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_three (n + 1), c_one_two n]

theorem c_two_four (n : Nat) :
    (c (n + 2)).2.2.2 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 0 1 0 0 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_four (n + 1), c_one_three n]

theorem c_three_one (n : Nat) :
    (c (n + 3)).1 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 1 2 1 1 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_one (n + 2), c_two_two n, c_two_three n, c_two_four n, lin_add, lin_add]

theorem c_three_two (n : Nat) :
    (c (n + 3)).2.1 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 1 1 1 0 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_two (n + 2), c_two_one n]

theorem c_three_three (n : Nat) :
    (c (n + 3)).2.2.1 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 0 1 1 1 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_three (n + 2), c_two_two n]

theorem c_three_four (n : Nat) :
    (c (n + 3)).2.2.2 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 1 0 0 0 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_four (n + 2), c_two_three n]

theorem c_four_one (n : Nat) :
    (c (n + 4)).1 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 2 2 2 1 := by
  rw [show n + 4 = (n + 3) + 1 by rfl]
  rw [c_step_one (n + 3), c_three_two n, c_three_three n, c_three_four n, lin_add, lin_add]

theorem c_four_two (n : Nat) :
    (c (n + 4)).2.1 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 1 2 1 1 := by
  rw [show n + 4 = (n + 3) + 1 by rfl]
  rw [c_step_two (n + 3), c_three_one n]

theorem c_four_three (n : Nat) :
    (c (n + 4)).2.2.1 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 1 1 1 0 := by
  rw [show n + 4 = (n + 3) + 1 by rfl]
  rw [c_step_three (n + 3), c_three_two n]

theorem c_four_four (n : Nat) :
    (c (n + 4)).2.2.2 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 0 1 1 1 := by
  rw [show n + 4 = (n + 3) + 1 by rfl]
  rw [c_step_four (n + 3), c_three_three n]

theorem S_base_lin (n : Nat) :
    S n = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 1 2 1 1 := by
  unfold S
  unfold lin
  rw [Nat.one_mul, Nat.one_mul, Nat.one_mul]

theorem S_one_lin (n : Nat) :
    S (n + 1) = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 2 2 2 1 := by
  unfold S
  rw [c_one_one n, c_one_two n, c_one_three n, c_one_four n,
      lin_two, lin_add, lin_add, lin_add]

theorem S_two_lin (n : Nat) :
    S (n + 2) = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 2 4 3 2 := by
  unfold S
  rw [c_two_one n, c_two_two n, c_two_three n, c_two_four n,
      lin_two, lin_add, lin_add, lin_add]

theorem S_three_lin (n : Nat) :
    S (n + 3) = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 4 5 4 2 := by
  unfold S
  rw [c_three_one n, c_three_two n, c_three_three n, c_three_four n,
      lin_two, lin_add, lin_add, lin_add]

theorem S_four_lin (n : Nat) :
    S (n + 4) = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 5 8 6 4 := by
  unfold S
  rw [c_four_one n, c_four_two n, c_four_three n, c_four_four n,
      lin_two, lin_add, lin_add, lin_add]

theorem theta_sparse_recurrence (n : Nat) :
    S (n + 4) = S (n + 2) + S (n + 1) + S n := by
  rw [S_four_lin n, S_two_lin n, S_one_lin n, S_base_lin n, lin_add, lin_add]

end BEDC.Derived.Window6ThetaSparseRecurrence
