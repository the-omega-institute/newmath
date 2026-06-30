namespace BEDC.Derived.Window6RisingColumnTripleRecurrence

/-- Nonnegative three-state transfer for rising-column triples. -/
def c : Nat → Nat × Nat × Nat
  | 0 => (1, 0, 0)
  | n + 1 =>
      let a := (c n).1
      let b := (c n).2.1
      let c2 := (c n).2.2
      (a + b + c2, 3 * a, 4 * a + b)

def A (m : Nat) : Nat := ((c m).1 + (c m).2.1) + (c m).2.2

theorem A_zero : A 0 = 1 := rfl
theorem A_one : A 1 = 8 := rfl
theorem A_two : A 2 = 18 := rfl
theorem A_three : A 3 = 77 := rfl

/-- Balanced three-term linear form over the current transfer state. -/
def lin (a b e p q r : Nat) : Nat := (p * a + q * b) + r * e

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
theorem lin_add (a b e p q r p' q' r' : Nat) :
    lin a b e p q r + lin a b e p' q' r'
      = lin a b e (p + p') (q + q') (r + r') := by
  unfold lin
  rw [swap_mid (p * a + q * b) (r * e) (p' * a + q' * b) (r' * e),
      swap_mid (p * a) (q * b) (p' * a) (q' * b),
      ← add_mul_pure p p' a, ← add_mul_pure q q' b,
      ← add_mul_pure r r' e]

/-- Scalar multiplication distributes over the linear form. -/
theorem lin_scale (a b e k p q r : Nat) :
    k * lin a b e p q r = lin a b e (k * p) (k * q) (k * r) := by
  unfold lin
  rw [Nat.mul_add k (p * a + q * b) (r * e),
      Nat.mul_add k (p * a) (q * b),
      ← mul_assoc_pure k p a, ← mul_assoc_pure k q b,
      ← mul_assoc_pure k r e]

theorem c_step_one (n : Nat) :
    (c (n + 1)).1 = ((c n).1 + (c n).2.1) + (c n).2.2 := rfl

theorem c_step_two (n : Nat) :
    (c (n + 1)).2.1 = 3 * (c n).1 := rfl

theorem c_step_three (n : Nat) :
    (c (n + 1)).2.2 = 4 * (c n).1 + (c n).2.1 := rfl

theorem c_one_one (n : Nat) :
    (c (n + 1)).1 = lin (c n).1 (c n).2.1 (c n).2.2 1 1 1 := by
  rw [c_step_one n]
  unfold lin
  rw [Nat.one_mul, Nat.one_mul, Nat.one_mul]

theorem c_one_two (n : Nat) :
    (c (n + 1)).2.1 = lin (c n).1 (c n).2.1 (c n).2.2 3 0 0 := by
  rw [c_step_two n]
  unfold lin
  rw [Nat.zero_mul, Nat.zero_mul, Nat.add_zero]

theorem c_one_three (n : Nat) :
    (c (n + 1)).2.2 = lin (c n).1 (c n).2.1 (c n).2.2 4 1 0 := by
  rw [c_step_three n]
  unfold lin
  rw [Nat.one_mul, Nat.zero_mul, Nat.add_zero]

theorem c_two_one (n : Nat) :
    (c (n + 2)).1 = lin (c n).1 (c n).2.1 (c n).2.2 8 2 1 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_one (n + 1), c_one_one n, c_one_two n, c_one_three n, lin_add, lin_add]

theorem c_two_two (n : Nat) :
    (c (n + 2)).2.1 = lin (c n).1 (c n).2.1 (c n).2.2 3 3 3 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_two (n + 1), c_one_one n,
      lin_scale (c n).1 (c n).2.1 (c n).2.2 3 1 1 1]

theorem c_two_three (n : Nat) :
    (c (n + 2)).2.2 = lin (c n).1 (c n).2.1 (c n).2.2 7 4 4 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_three (n + 1), c_one_one n, c_one_two n,
      lin_scale (c n).1 (c n).2.1 (c n).2.2 4 1 1 1,
      lin_add]

theorem c_three_one (n : Nat) :
    (c (n + 3)).1 = lin (c n).1 (c n).2.1 (c n).2.2 18 9 8 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_one (n + 2), c_two_one n, c_two_two n, c_two_three n, lin_add, lin_add]

theorem c_three_two (n : Nat) :
    (c (n + 3)).2.1 = lin (c n).1 (c n).2.1 (c n).2.2 24 6 3 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_two (n + 2), c_two_one n,
      lin_scale (c n).1 (c n).2.1 (c n).2.2 3 8 2 1]

theorem c_three_three (n : Nat) :
    (c (n + 3)).2.2 = lin (c n).1 (c n).2.1 (c n).2.2 35 11 7 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_three (n + 2), c_two_one n, c_two_two n,
      lin_scale (c n).1 (c n).2.1 (c n).2.2 4 8 2 1,
      lin_add]

theorem A_base_lin (n : Nat) :
    A n = lin (c n).1 (c n).2.1 (c n).2.2 1 1 1 := by
  unfold A
  unfold lin
  rw [Nat.one_mul, Nat.one_mul, Nat.one_mul]

theorem A_one_lin (n : Nat) :
    A (n + 1) = lin (c n).1 (c n).2.1 (c n).2.2 8 2 1 := by
  unfold A
  rw [c_one_one n, c_one_two n, c_one_three n, lin_add, lin_add]

theorem A_two_lin (n : Nat) :
    A (n + 2) = lin (c n).1 (c n).2.1 (c n).2.2 18 9 8 := by
  unfold A
  rw [c_two_one n, c_two_two n, c_two_three n, lin_add, lin_add]

theorem A_three_lin (n : Nat) :
    A (n + 3) = lin (c n).1 (c n).2.1 (c n).2.2 77 26 18 := by
  unfold A
  rw [c_three_one n, c_three_two n, c_three_three n, lin_add, lin_add]

theorem rising_column_triple_recurrence (n : Nat) :
    A (n + 3) = A (n + 2) + 7 * A (n + 1) + 3 * A n := by
  rw [A_three_lin n, A_two_lin n, A_one_lin n, A_base_lin n,
      lin_scale (c n).1 (c n).2.1 (c n).2.2 7 8 2 1,
      lin_scale (c n).1 (c n).2.1 (c n).2.2 3 1 1 1,
      lin_add, lin_add]

end BEDC.Derived.Window6RisingColumnTripleRecurrence
