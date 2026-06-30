namespace BEDC.Derived.Window6CyclicOrthogonalityQuartetRecurrence

/-- Nonnegative three-state transfer for cyclic-orthogonality quartets. -/
def c : Nat → Nat × Nat × Nat
  | 0 => (1, 0, 0)
  | n + 1 =>
      let a := (c n).1
      let b := (c n).2.1
      let c2 := (c n).2.2
      (a + b + c2, 4 * a + 3 * b + 2 * c2, 2 * a + b + c2)

def Z (m : Nat) : Nat := ((c m).1 + (c m).2.1) + (c m).2.2

theorem Z_zero : Z 0 = 1 := rfl
theorem Z_one : Z 1 = 7 := rfl
theorem Z_two : Z 2 = 35 := rfl
theorem Z_three : Z 3 = 181 := rfl

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
    (c (n + 1)).2.1 = (4 * (c n).1 + 3 * (c n).2.1) + 2 * (c n).2.2 := rfl

theorem c_step_three (n : Nat) :
    (c (n + 1)).2.2 = (2 * (c n).1 + (c n).2.1) + (c n).2.2 := rfl

theorem c_one_one (n : Nat) :
    (c (n + 1)).1 = lin (c n).1 (c n).2.1 (c n).2.2 1 1 1 := by
  rw [c_step_one n]
  unfold lin
  rw [Nat.one_mul, Nat.one_mul, Nat.one_mul]

theorem c_one_two (n : Nat) :
    (c (n + 1)).2.1 = lin (c n).1 (c n).2.1 (c n).2.2 4 3 2 := by
  rw [c_step_two n]
  unfold lin
  rfl

theorem c_one_three (n : Nat) :
    (c (n + 1)).2.2 = lin (c n).1 (c n).2.1 (c n).2.2 2 1 1 := by
  rw [c_step_three n]
  unfold lin
  rw [Nat.one_mul, Nat.one_mul]

theorem c_two_one (n : Nat) :
    (c (n + 2)).1 = lin (c n).1 (c n).2.1 (c n).2.2 7 5 4 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_one (n + 1), c_one_one n, c_one_two n, c_one_three n, lin_add, lin_add]

theorem c_two_two (n : Nat) :
    (c (n + 2)).2.1 = lin (c n).1 (c n).2.1 (c n).2.2 20 15 12 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_two (n + 1), c_one_one n, c_one_two n, c_one_three n,
      lin_scale (c n).1 (c n).2.1 (c n).2.2 4 1 1 1,
      lin_scale (c n).1 (c n).2.1 (c n).2.2 3 4 3 2,
      lin_scale (c n).1 (c n).2.1 (c n).2.2 2 2 1 1,
      lin_add, lin_add]

theorem c_two_three (n : Nat) :
    (c (n + 2)).2.2 = lin (c n).1 (c n).2.1 (c n).2.2 8 6 5 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_three (n + 1), c_one_one n, c_one_two n, c_one_three n,
      lin_scale (c n).1 (c n).2.1 (c n).2.2 2 1 1 1,
      lin_add, lin_add]

theorem c_three_one (n : Nat) :
    (c (n + 3)).1 = lin (c n).1 (c n).2.1 (c n).2.2 35 26 21 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_one (n + 2), c_two_one n, c_two_two n, c_two_three n, lin_add, lin_add]

theorem c_three_two (n : Nat) :
    (c (n + 3)).2.1 = lin (c n).1 (c n).2.1 (c n).2.2 104 77 62 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_two (n + 2), c_two_one n, c_two_two n, c_two_three n,
      lin_scale (c n).1 (c n).2.1 (c n).2.2 4 7 5 4,
      lin_scale (c n).1 (c n).2.1 (c n).2.2 3 20 15 12,
      lin_scale (c n).1 (c n).2.1 (c n).2.2 2 8 6 5,
      lin_add, lin_add]

theorem c_three_three (n : Nat) :
    (c (n + 3)).2.2 = lin (c n).1 (c n).2.1 (c n).2.2 42 31 25 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_three (n + 2), c_two_one n, c_two_two n, c_two_three n,
      lin_scale (c n).1 (c n).2.1 (c n).2.2 2 7 5 4,
      lin_add, lin_add]

theorem Z_base_lin (n : Nat) :
    Z n = lin (c n).1 (c n).2.1 (c n).2.2 1 1 1 := by
  unfold Z
  unfold lin
  rw [Nat.one_mul, Nat.one_mul, Nat.one_mul]

theorem Z_one_lin (n : Nat) :
    Z (n + 1) = lin (c n).1 (c n).2.1 (c n).2.2 7 5 4 := by
  unfold Z
  rw [c_one_one n, c_one_two n, c_one_three n, lin_add, lin_add]

theorem Z_two_lin (n : Nat) :
    Z (n + 2) = lin (c n).1 (c n).2.1 (c n).2.2 35 26 21 := by
  unfold Z
  rw [c_two_one n, c_two_two n, c_two_three n, lin_add, lin_add]

theorem Z_three_lin (n : Nat) :
    Z (n + 3) = lin (c n).1 (c n).2.1 (c n).2.2 181 134 108 := by
  unfold Z
  rw [c_three_one n, c_three_two n, c_three_three n, lin_add, lin_add]

theorem cyclic_orthogonality_quartet_recurrence (n : Nat) :
    Z (n + 3) + Z n = 5 * Z (n + 2) + Z (n + 1) := by
  rw [Z_three_lin n, Z_base_lin n, Z_two_lin n, Z_one_lin n,
      lin_add,
      lin_scale (c n).1 (c n).2.1 (c n).2.2 5 35 26 21,
      lin_add]

end BEDC.Derived.Window6CyclicOrthogonalityQuartetRecurrence
