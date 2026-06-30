namespace BEDC.Derived.Window6BetweennessOrderFour

/-- Nonnegative four-state transfer. `c n = (a,b,e,f)`;
betweenness triple count `A m = (c m).1`. -/
def c : Nat → Nat × Nat × Nat × Nat
  | 0 => (1, 2, 2, 1)
  | n + 1 =>
      let a := (c n).1
      let b := (c n).2.1
      let e := (c n).2.2.1
      let f := (c n).2.2.2
      ((a + b) + (e + f), (a + a) + (b + e), (a + a) + b, a)

def A (m : Nat) : Nat := (c m).1

theorem A_zero : A 0 = 1 := rfl
theorem A_one : A 1 = 6 := rfl
theorem A_two : A 2 = 17 := rfl
theorem A_three : A 3 = 63 := rfl
theorem A_four : A 4 = 210 := rfl

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

/-- Scalar multiplication by five distributes over the linear form. -/
theorem lin_five (a b e f p q r s : Nat) :
    5 * lin a b e f p q r s = lin a b e f (5 * p) (5 * q) (5 * r) (5 * s) := by
  unfold lin
  rw [Nat.mul_add 5 (p * a + q * b) (r * e + s * f),
      Nat.mul_add 5 (p * a) (q * b), Nat.mul_add 5 (r * e) (s * f),
      ← mul_assoc_pure 5 p a, ← mul_assoc_pure 5 q b,
      ← mul_assoc_pure 5 r e, ← mul_assoc_pure 5 s f]

theorem c_step_one (n : Nat) :
    (c (n + 1)).1 =
      ((c n).1 + (c n).2.1) + ((c n).2.2.1 + (c n).2.2.2) := rfl

theorem c_step_two (n : Nat) :
    (c (n + 1)).2.1 =
      ((c n).1 + (c n).1) + ((c n).2.1 + (c n).2.2.1) := rfl

theorem c_step_three (n : Nat) :
    (c (n + 1)).2.2.1 = ((c n).1 + (c n).1) + (c n).2.1 := rfl

theorem c_step_four (n : Nat) :
    (c (n + 1)).2.2.2 = (c n).1 := rfl

theorem c_one_one (n : Nat) :
    (c (n + 1)).1 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 1 1 1 1 := by
  rw [c_step_one n]
  unfold lin
  rw [Nat.one_mul, Nat.one_mul, Nat.one_mul, Nat.one_mul]

theorem c_one_two (n : Nat) :
    (c (n + 1)).2.1 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 2 1 1 0 := by
  rw [c_step_two n]
  unfold lin
  rw [Nat.two_mul, Nat.one_mul, Nat.one_mul, Nat.zero_mul, Nat.add_zero]
  rw [Nat.add_assoc ((c n).1 + (c n).1) (c n).2.1 (c n).2.2.1]

theorem c_one_three (n : Nat) :
    (c (n + 1)).2.2.1 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 2 1 0 0 := by
  rw [c_step_three n]
  unfold lin
  rw [Nat.two_mul, Nat.one_mul, Nat.zero_mul, Nat.zero_mul, Nat.add_zero]

theorem c_one_four (n : Nat) :
    (c (n + 1)).2.2.2 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 1 0 0 0 := by
  rw [c_step_four n]
  unfold lin
  rw [Nat.one_mul, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul, Nat.add_zero]

theorem c_two_one (n : Nat) :
    (c (n + 2)).1 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 6 3 2 1 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_one (n + 1), c_one_one n, c_one_two n, c_one_three n, c_one_four n,
      lin_add, lin_add, lin_add]

theorem c_two_two (n : Nat) :
    (c (n + 2)).2.1 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 6 4 3 2 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_two (n + 1), ← Nat.two_mul (c (n + 1)).1,
      c_one_one n, c_one_two n, c_one_three n,
      lin_two, lin_add, lin_add]

theorem c_two_three (n : Nat) :
    (c (n + 2)).2.2.1 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 4 3 3 2 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_three (n + 1), ← Nat.two_mul (c (n + 1)).1,
      c_one_one n, c_one_two n,
      lin_two, lin_add]

theorem c_two_four (n : Nat) :
    (c (n + 2)).2.2.2 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 1 1 1 1 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_four (n + 1), c_one_one n]

theorem c_three_one (n : Nat) :
    (c (n + 3)).1 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 17 11 9 6 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_one (n + 2), c_two_one n, c_two_two n, c_two_three n, c_two_four n,
      lin_add, lin_add, lin_add]

theorem c_three_two (n : Nat) :
    (c (n + 3)).2.1 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 22 13 10 6 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_two (n + 2), ← Nat.two_mul (c (n + 2)).1,
      c_two_one n, c_two_two n, c_two_three n,
      lin_two, lin_add, lin_add]

theorem c_three_three (n : Nat) :
    (c (n + 3)).2.2.1 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 18 10 7 4 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_three (n + 2), ← Nat.two_mul (c (n + 2)).1,
      c_two_one n, c_two_two n,
      lin_two, lin_add]

theorem c_three_four (n : Nat) :
    (c (n + 3)).2.2.2 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 6 3 2 1 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_four (n + 2), c_two_one n]

theorem c_four_one (n : Nat) :
    (c (n + 4)).1 = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 63 37 28 17 := by
  rw [show n + 4 = (n + 3) + 1 by rfl]
  rw [c_step_one (n + 3), c_three_one n, c_three_two n, c_three_three n, c_three_four n,
      lin_add, lin_add, lin_add]

theorem A_base_lin (n : Nat) :
    A n = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 1 0 0 0 := by
  unfold A
  unfold lin
  rw [Nat.one_mul, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul, Nat.add_zero]

theorem A_two_lin (n : Nat) :
    A (n + 2) = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 6 3 2 1 := by
  unfold A
  rw [c_two_one n]

theorem A_three_lin (n : Nat) :
    A (n + 3) = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 17 11 9 6 := by
  unfold A
  rw [c_three_one n]

theorem A_four_lin (n : Nat) :
    A (n + 4) = lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2 63 37 28 17 := by
  unfold A
  rw [c_four_one n]

theorem betweenness_order_four (n : Nat) :
    A (n + 4) + A n = 2 * A (n + 3) + 5 * A (n + 2) := by
  rw [A_four_lin n, A_base_lin n, A_three_lin n, A_two_lin n,
      lin_add, lin_two, lin_five, lin_add]

end BEDC.Derived.Window6BetweennessOrderFour
