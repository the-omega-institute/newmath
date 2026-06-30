namespace BEDC.Derived.Window6AdditiveEnergyRecurrence

/-- Nonnegative three-state transfer. `c n = (p,q,r)`;
Fibonacci-cube additive energy is read out by `E m`. -/
def c : Nat → Nat × Nat × Nat
  | 0 => (1, 0, 0)
  | n + 1 =>
      let p := (c n).1
      let q := (c n).2.1
      let r := (c n).2.2
      ((p + 6 * q) + r, p + q, p)

def E (m : Nat) : Nat := (c m).1 + 6 * (c m).2.1 + (c m).2.2

theorem E_zero : E 0 = 1 := rfl
theorem E_one : E 1 = 8 := rfl
theorem E_two : E 2 = 21 := rfl
theorem E_three : E 3 = 89 := rfl
theorem E_four : E 4 = 296 := rfl

/-- Balanced three-term linear form. -/
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

/-- Scalar multiplication by two distributes over the linear form. -/
theorem lin_two (a b e p q r : Nat) :
    2 * lin a b e p q r = lin a b e (2 * p) (2 * q) (2 * r) := by
  unfold lin
  rw [Nat.mul_add 2 (p * a + q * b) (r * e),
      Nat.mul_add 2 (p * a) (q * b),
      ← mul_assoc_pure 2 p a, ← mul_assoc_pure 2 q b,
      ← mul_assoc_pure 2 r e]

/-- Scalar multiplication by six distributes over the linear form. -/
theorem lin_six (a b e p q r : Nat) :
    6 * lin a b e p q r = lin a b e (6 * p) (6 * q) (6 * r) := by
  unfold lin
  rw [Nat.mul_add 6 (p * a + q * b) (r * e),
      Nat.mul_add 6 (p * a) (q * b),
      ← mul_assoc_pure 6 p a, ← mul_assoc_pure 6 q b,
      ← mul_assoc_pure 6 r e]

theorem c_step_one (n : Nat) :
    (c (n + 1)).1 = ((c n).1 + 6 * (c n).2.1) + (c n).2.2 := rfl

theorem c_step_two (n : Nat) :
    (c (n + 1)).2.1 = (c n).1 + (c n).2.1 := rfl

theorem c_step_three (n : Nat) :
    (c (n + 1)).2.2 = (c n).1 := rfl

theorem c_one_one (n : Nat) :
    (c (n + 1)).1 = lin (c n).1 (c n).2.1 (c n).2.2 1 6 1 := by
  rw [c_step_one n]
  unfold lin
  rw [Nat.one_mul, Nat.one_mul]

theorem c_one_two (n : Nat) :
    (c (n + 1)).2.1 = lin (c n).1 (c n).2.1 (c n).2.2 1 1 0 := by
  rw [c_step_two n]
  unfold lin
  rw [Nat.one_mul, Nat.one_mul, Nat.zero_mul, Nat.add_zero]

theorem c_one_three (n : Nat) :
    (c (n + 1)).2.2 = lin (c n).1 (c n).2.1 (c n).2.2 1 0 0 := by
  rw [c_step_three n]
  unfold lin
  rw [Nat.one_mul, Nat.zero_mul, Nat.zero_mul, Nat.add_zero]

theorem c_two_one (n : Nat) :
    (c (n + 2)).1 = lin (c n).1 (c n).2.1 (c n).2.2 8 12 1 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_one (n + 1), c_one_one n, c_one_two n, c_one_three n,
      lin_six (c n).1 (c n).2.1 (c n).2.2 1 1 0, lin_add, lin_add]

theorem c_two_two (n : Nat) :
    (c (n + 2)).2.1 = lin (c n).1 (c n).2.1 (c n).2.2 2 7 1 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_two (n + 1), c_one_one n, c_one_two n, lin_add]

theorem c_two_three (n : Nat) :
    (c (n + 2)).2.2 = lin (c n).1 (c n).2.1 (c n).2.2 1 6 1 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_three (n + 1), c_one_one n]

theorem c_three_one (n : Nat) :
    (c (n + 3)).1 = lin (c n).1 (c n).2.1 (c n).2.2 21 60 8 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_one (n + 2), c_two_one n, c_two_two n, c_two_three n,
      lin_six (c n).1 (c n).2.1 (c n).2.2 2 7 1, lin_add, lin_add]

theorem c_three_two (n : Nat) :
    (c (n + 3)).2.1 = lin (c n).1 (c n).2.1 (c n).2.2 10 19 2 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_two (n + 2), c_two_one n, c_two_two n, lin_add]

theorem c_three_three (n : Nat) :
    (c (n + 3)).2.2 = lin (c n).1 (c n).2.1 (c n).2.2 8 12 1 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_three (n + 2), c_two_one n]

theorem E_base_lin (n : Nat) :
    E n = lin (c n).1 (c n).2.1 (c n).2.2 1 6 1 := by
  unfold E
  unfold lin
  rw [Nat.one_mul, Nat.one_mul]

theorem E_one_lin (n : Nat) :
    E (n + 1) = lin (c n).1 (c n).2.1 (c n).2.2 8 12 1 := by
  unfold E
  rw [c_one_one n, c_one_two n, c_one_three n,
      lin_six (c n).1 (c n).2.1 (c n).2.2 1 1 0, lin_add, lin_add]

theorem E_two_lin (n : Nat) :
    E (n + 2) = lin (c n).1 (c n).2.1 (c n).2.2 21 60 8 := by
  unfold E
  rw [c_two_one n, c_two_two n, c_two_three n,
      lin_six (c n).1 (c n).2.1 (c n).2.2 2 7 1, lin_add, lin_add]

theorem E_three_lin (n : Nat) :
    E (n + 3) = lin (c n).1 (c n).2.1 (c n).2.2 89 186 21 := by
  unfold E
  rw [c_three_one n, c_three_two n, c_three_three n,
      lin_six (c n).1 (c n).2.1 (c n).2.2 10 19 2, lin_add, lin_add]

theorem additive_energy_recurrence (n : Nat) :
    E (n + 3) + E n = 2 * E (n + 2) + 6 * E (n + 1) := by
  rw [E_three_lin n, E_base_lin n, E_two_lin n, E_one_lin n,
      lin_add, lin_two, lin_six, lin_add]

end BEDC.Derived.Window6AdditiveEnergyRecurrence
