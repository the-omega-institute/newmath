namespace BEDC.Derived.Window6GatedFaceRecurrence

/-- Nonnegative three-state transfer for coordinate-gated Fibonacci-cube faces. -/
def c : Nat → Nat × Nat × Nat
  | 0 => (1, 0, 0)
  | n + 1 =>
      let a := (c n).1
      let b := (c n).2.1
      let d := (c n).2.2
      (a + b, (a + b) + d, b)

def C (m : Nat) : Nat := (c m).1 + 2 * (c m).2.1

theorem C_zero : C 0 = 1 := rfl
theorem C_one : C 1 = 3 := rfl
theorem C_two : C 2 = 6 := rfl
theorem C_three : C 3 = 14 := rfl
theorem C_four : C 4 = 31 := rfl

/-- Balanced three-term linear form. -/
def lin (a b d p q r : Nat) : Nat := (p * a + q * b) + r * d

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
theorem lin_add (a b d p q r p' q' r' : Nat) :
    lin a b d p q r + lin a b d p' q' r'
      = lin a b d (p + p') (q + q') (r + r') := by
  unfold lin
  rw [swap_mid (p * a + q * b) (r * d) (p' * a + q' * b) (r' * d),
      swap_mid (p * a) (q * b) (p' * a) (q' * b),
      ← add_mul_pure p p' a, ← add_mul_pure q q' b,
      ← add_mul_pure r r' d]

/-- Scalar multiplication by two distributes over the linear form. -/
theorem lin_two (a b d p q r : Nat) :
    2 * lin a b d p q r = lin a b d (2 * p) (2 * q) (2 * r) := by
  unfold lin
  rw [Nat.mul_add 2 (p * a + q * b) (r * d),
      Nat.mul_add 2 (p * a) (q * b),
      ← mul_assoc_pure 2 p a, ← mul_assoc_pure 2 q b,
      ← mul_assoc_pure 2 r d]

theorem c_step_one (n : Nat) :
    (c (n + 1)).1 = (c n).1 + (c n).2.1 := rfl

theorem c_step_two (n : Nat) :
    (c (n + 1)).2.1 = ((c n).1 + (c n).2.1) + (c n).2.2 := rfl

theorem c_step_three (n : Nat) :
    (c (n + 1)).2.2 = (c n).2.1 := rfl

theorem c_one_one (n : Nat) :
    (c (n + 1)).1 = lin (c n).1 (c n).2.1 (c n).2.2 1 1 0 := by
  rw [c_step_one n]
  unfold lin
  rw [Nat.one_mul, Nat.one_mul, Nat.zero_mul, Nat.add_zero]

theorem c_one_two (n : Nat) :
    (c (n + 1)).2.1 = lin (c n).1 (c n).2.1 (c n).2.2 1 1 1 := by
  rw [c_step_two n]
  unfold lin
  rw [Nat.one_mul, Nat.one_mul, Nat.one_mul]

theorem c_one_three (n : Nat) :
    (c (n + 1)).2.2 = lin (c n).1 (c n).2.1 (c n).2.2 0 1 0 := by
  rw [c_step_three n]
  unfold lin
  rw [Nat.zero_mul, Nat.one_mul, Nat.zero_mul, Nat.zero_add, Nat.add_zero]

theorem c_two_one (n : Nat) :
    (c (n + 2)).1 = lin (c n).1 (c n).2.1 (c n).2.2 2 2 1 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_one (n + 1), c_one_one n, c_one_two n, lin_add]

theorem c_two_two (n : Nat) :
    (c (n + 2)).2.1 = lin (c n).1 (c n).2.1 (c n).2.2 2 3 1 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_two (n + 1), c_one_one n, c_one_two n, c_one_three n, lin_add, lin_add]

theorem c_two_three (n : Nat) :
    (c (n + 2)).2.2 = lin (c n).1 (c n).2.1 (c n).2.2 1 1 1 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_three (n + 1), c_one_two n]

theorem c_three_one (n : Nat) :
    (c (n + 3)).1 = lin (c n).1 (c n).2.1 (c n).2.2 4 5 2 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_one (n + 2), c_two_one n, c_two_two n, lin_add]

theorem c_three_two (n : Nat) :
    (c (n + 3)).2.1 = lin (c n).1 (c n).2.1 (c n).2.2 5 6 3 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_two (n + 2), c_two_one n, c_two_two n, c_two_three n, lin_add, lin_add]

theorem c_three_three (n : Nat) :
    (c (n + 3)).2.2 = lin (c n).1 (c n).2.1 (c n).2.2 2 3 1 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_three (n + 2), c_two_two n]

theorem C_base_lin (n : Nat) :
    C n = lin (c n).1 (c n).2.1 (c n).2.2 1 2 0 := by
  unfold C
  unfold lin
  rw [Nat.one_mul, Nat.zero_mul, Nat.add_zero]

theorem C_one_lin (n : Nat) :
    C (n + 1) = lin (c n).1 (c n).2.1 (c n).2.2 3 3 2 := by
  unfold C
  rw [c_one_one n, c_one_two n, lin_two, lin_add]

theorem C_two_lin (n : Nat) :
    C (n + 2) = lin (c n).1 (c n).2.1 (c n).2.2 6 8 3 := by
  unfold C
  rw [c_two_one n, c_two_two n, lin_two, lin_add]

theorem C_three_lin (n : Nat) :
    C (n + 3) = lin (c n).1 (c n).2.1 (c n).2.2 14 17 8 := by
  unfold C
  rw [c_three_one n, c_three_two n, lin_two, lin_add]

theorem gated_face_recurrence (n : Nat) :
    C (n + 3) + C n = 2 * C (n + 2) + C (n + 1) := by
  rw [C_three_lin n, C_base_lin n, C_two_lin n, C_one_lin n,
      lin_add, lin_two, lin_add]

end BEDC.Derived.Window6GatedFaceRecurrence
