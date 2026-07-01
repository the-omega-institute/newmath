namespace BEDC.Derived.Window6PosetComparabilityJacobsthal

/-- Balanced two-term linear form over the current transfer state. -/
def lin (a b p q : Nat) : Nat := p * a + q * b

/-- Two-state nonnegative transfer for the poset comparability count. -/
def c : Nat → Nat × Nat
  | 0 => (1, 3)
  | n + 1 =>
      let a := (c n).1
      let b := (c n).2
      (b, b + 2 * a)

def C (m : Nat) : Nat := (c m).1

theorem C_zero : C 0 = 1 := rfl

theorem C_one : C 1 = 3 := rfl

theorem C_two : C 2 = 5 := rfl

theorem C_three : C 3 = 11 := rfl

theorem add_mul_pure (p q a : Nat) : (p + q) * a = p * a + q * a := by
  induction a with
  | zero =>
      rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero, Nat.add_zero]
  | succ a ih =>
      rw [Nat.mul_add (p + q) a 1, Nat.mul_add p a 1, Nat.mul_add q a 1,
        Nat.mul_one, Nat.mul_one, Nat.mul_one, ih]
      rw [Nat.add_assoc (p * a) (q * a) (p + q), Nat.add_left_comm (q * a) p q,
        ← Nat.add_assoc (p * a) p (q * a + q)]

theorem mul_assoc_pure (p q a : Nat) : (p * q) * a = p * (q * a) := by
  induction a with
  | zero =>
      rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | succ a ih =>
      rw [Nat.mul_add (p * q) a 1, Nat.mul_one, Nat.mul_add q a 1, Nat.mul_one,
        Nat.mul_add p (q * a) q, ih]

/-- Addition of two linear forms over the same basis. -/
theorem lin_add (a b p q p' q' : Nat) :
    lin a b p q + lin a b p' q' = lin a b (p + p') (q + q') := by
  unfold lin
  rw [Nat.add_assoc (p * a) (q * b) (p' * a + q' * b),
    Nat.add_left_comm (q * b) (p' * a) (q' * b),
    ← Nat.add_assoc (p * a) (p' * a) (q * b + q' * b),
    ← add_mul_pure p p' a, ← add_mul_pure q q' b]

/-- Scalar multiplication distributes over the linear form. -/
theorem lin_scale (a b k p q : Nat) :
    k * lin a b p q = lin a b (k * p) (k * q) := by
  unfold lin
  rw [Nat.mul_add k (p * a) (q * b), ← mul_assoc_pure k p a, ← mul_assoc_pure k q b]

theorem c_step_one (n : Nat) : (c (n + 1)).1 = (c n).2 := rfl

theorem c_step_two (n : Nat) : (c (n + 1)).2 = (c n).2 + 2 * (c n).1 := rfl

theorem c_one_one (n : Nat) : (c (n + 1)).1 = lin (c n).1 (c n).2 0 1 := by
  rw [c_step_one n]
  unfold lin
  rw [Nat.zero_mul, Nat.one_mul, Nat.zero_add]

theorem c_one_two (n : Nat) : (c (n + 1)).2 = lin (c n).1 (c n).2 2 1 := by
  rw [c_step_two n]
  unfold lin
  rw [Nat.one_mul, Nat.add_comm]

theorem C_base_lin (n : Nat) : C n = lin (c n).1 (c n).2 1 0 := by
  unfold C
  unfold lin
  rw [Nat.one_mul, Nat.zero_mul, Nat.add_zero]

theorem C_one_lin (n : Nat) : C (n + 1) = lin (c n).1 (c n).2 0 1 := by
  unfold C
  rw [c_one_one n]

theorem C_two_lin (n : Nat) : C (n + 2) = lin (c n).1 (c n).2 2 1 := by
  show (c (n + 2)).1 = _
  rw [show n + 2 = (n + 1) + 1 by rfl, c_step_one (n + 1), c_one_two n]

theorem poset_comparability_recurrence (n : Nat) :
    C (n + 2) = C (n + 1) + 2 * C n := by
  rw [C_two_lin n, C_one_lin n, C_base_lin n,
    lin_scale (c n).1 (c n).2 2 1 0, lin_add]

end BEDC.Derived.Window6PosetComparabilityJacobsthal
