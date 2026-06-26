namespace BEDC.Derived.Window6SixfoldWalshRecurrence

/-- Nonnegative four-state transfer for the sixfold Walsh/XOR zero-sum count. -/
def c : Nat → Nat × Nat × Nat × Nat
  | 0 => (1, 1, 1, 1)
  | n + 1 =>
      let a := (c n).1
      let b := (c n).2.1
      let e := (c n).2.2.1
      let f := (c n).2.2.2
      ((a + 15 * b) + (15 * e + f), (a + 6 * b) + e, a + b, a)

def H (m : Nat) : Nat := (c m).1

theorem H_zero : H 0 = 1 := rfl
theorem H_one : H 1 = 32 := rfl
theorem H_two : H 2 = 183 := rfl
theorem H_three : H 3 = 2045 := rfl
theorem H_four : H 4 = 16928 := rfl

/-- Balanced four-term linear form over the current transfer state. -/
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

/-- Scalar multiplication distributes over the linear form. -/
theorem lin_scale (a b e f k p q r s : Nat) :
    k * lin a b e f p q r s = lin a b e f (k * p) (k * q) (k * r) (k * s) := by
  unfold lin
  rw [Nat.mul_add k (p * a + q * b) (r * e + s * f),
      Nat.mul_add k (p * a) (q * b), Nat.mul_add k (r * e) (s * f),
      ← mul_assoc_pure k p a, ← mul_assoc_pure k q b,
      ← mul_assoc_pure k r e, ← mul_assoc_pure k s f]

theorem c_step_one (n : Nat) :
    (c (n + 1)).1 =
      ((c n).1 + 15 * (c n).2.1) + (15 * (c n).2.2.1 + (c n).2.2.2) := rfl

theorem c_step_two (n : Nat) :
    (c (n + 1)).2.1 = ((c n).1 + 6 * (c n).2.1) + (c n).2.2.1 := rfl

theorem c_step_three (n : Nat) :
    (c (n + 1)).2.2.1 = (c n).1 + (c n).2.1 := rfl

theorem c_step_four (n : Nat) :
    (c (n + 1)).2.2.2 = (c n).1 := rfl

theorem c_one_one (n : Nat) :
    (c (n + 1)).1 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 1 15 15 1 := by
  rw [c_step_one n]
  unfold lin
  rw [Nat.one_mul, Nat.one_mul]

theorem c_one_two (n : Nat) :
    (c (n + 1)).2.1 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 1 6 1 0 := by
  rw [c_step_two n]
  unfold lin
  rw [Nat.one_mul, Nat.one_mul, Nat.zero_mul, Nat.add_zero]

theorem c_one_three (n : Nat) :
    (c (n + 1)).2.2.1 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 1 1 0 0 := by
  rw [c_step_three n]
  unfold lin
  rw [Nat.one_mul, Nat.one_mul, Nat.zero_mul, Nat.zero_mul, Nat.add_zero]

theorem c_one_four (n : Nat) :
    (c (n + 1)).2.2.2 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 1 0 0 0 := by
  rw [c_step_four n]
  unfold lin
  rw [Nat.one_mul, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul, Nat.add_zero]

theorem c_two_one (n : Nat) :
    (c (n + 2)).1 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 32 120 30 1 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_one (n + 1), c_one_one n, c_one_two n, c_one_three n, c_one_four n,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 15 1 6 1 0,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 15 1 1 0 0,
      lin_add, lin_add, lin_add]

theorem c_two_two (n : Nat) :
    (c (n + 2)).2.1 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 8 52 21 1 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_two (n + 1), c_one_one n, c_one_two n, c_one_three n,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 6 1 6 1 0,
      lin_add, lin_add]

theorem c_two_three (n : Nat) :
    (c (n + 2)).2.2.1 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 2 21 16 1 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_three (n + 1), c_one_one n, c_one_two n, lin_add]

theorem c_two_four (n : Nat) :
    (c (n + 2)).2.2.2 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 1 15 15 1 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_four (n + 1), c_one_one n]

theorem c_three_one (n : Nat) :
    (c (n + 3)).1 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 183 1230 600 32 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_one (n + 2), c_two_one n, c_two_two n, c_two_three n, c_two_four n,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 15 8 52 21 1,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 15 2 21 16 1,
      lin_add, lin_add, lin_add]

theorem c_three_two (n : Nat) :
    (c (n + 3)).2.1 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 82 453 172 8 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_two (n + 2), c_two_one n, c_two_two n, c_two_three n,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 6 8 52 21 1,
      lin_add, lin_add]

theorem c_three_three (n : Nat) :
    (c (n + 3)).2.2.1 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 40 172 51 2 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_three (n + 2), c_two_one n, c_two_two n, lin_add]

theorem c_three_four (n : Nat) :
    (c (n + 3)).2.2.2 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 32 120 30 1 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_four (n + 2), c_two_one n]

theorem c_four_one (n : Nat) :
    (c (n + 4)).1 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 2045 10725 3975 183 := by
  rw [show n + 4 = (n + 3) + 1 by rfl]
  rw [c_step_one (n + 3), c_three_one n, c_three_two n, c_three_three n, c_three_four n,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 15 82 453 172 8,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 15 40 172 51 2,
      lin_add, lin_add, lin_add]

theorem H_base_lin (n : Nat) :
    H n = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 1 0 0 0 := by
  unfold H
  unfold lin
  rw [Nat.one_mul, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul, Nat.add_zero]

theorem H_one_lin (n : Nat) :
    H (n + 1) = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 1 15 15 1 := by
  unfold H
  rw [c_one_one n]

theorem H_two_lin (n : Nat) :
    H (n + 2) = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 32 120 30 1 := by
  unfold H
  rw [c_two_one n]

theorem H_three_lin (n : Nat) :
    H (n + 3) = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 183 1230 600 32 := by
  unfold H
  rw [c_three_one n]

theorem H_four_lin (n : Nat) :
    H (n + 4) = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 2045 10725 3975 183 := by
  unfold H
  rw [c_four_one n]

theorem sixfold_walsh_recurrence (n : Nat) :
    H (n + 4) + 67 * H (n + 1) + H n = 7 * H (n + 3) + 26 * H (n + 2) := by
  rw [H_four_lin n, H_one_lin n, H_base_lin n, H_three_lin n, H_two_lin n,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 67 1 15 15 1,
      lin_add,
      lin_add,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 7 183 1230 600 32,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 26 32 120 30 1,
      lin_add]

end BEDC.Derived.Window6SixfoldWalshRecurrence
