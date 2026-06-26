namespace BEDC.Derived.Window6FlippabilityMaskRecurrence

/-- Nonnegative five-state transfer for Fibonacci-cube flippability-mask images. -/
def c : Nat → Nat × Nat × Nat × Nat × Nat
  | 0 => (1, 0, 1, 1, 1)
  | n + 1 =>
      let a := (c n).1
      let b := (c n).2.1
      let e := (c n).2.2.1
      let f := (c n).2.2.2.1
      let g := (c n).2.2.2.2
      (b + e, g, a + f, b + f, a)

def Phi (m : Nat) : Nat := (c m).1

theorem Phi_zero : Phi 0 = 1 := rfl
theorem Phi_one : Phi 1 = 1 := rfl
theorem Phi_two : Phi 2 = 3 := rfl
theorem Phi_three : Phi 3 = 3 := rfl
theorem Phi_four : Phi 4 = 6 := rfl
theorem Phi_five : Phi 5 = 9 := rfl

/-- Balanced five-term linear form over the current transfer state. -/
def lin (a b e f g p q r s t : Nat) : Nat := (((p * a + q * b) + (r * e + s * f)) + t * g)

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

theorem five_sum_add (x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : Nat) :
    ((((x1 + x2) + (x3 + x4)) + x5) + (((y1 + y2) + (y3 + y4)) + y5))
      = ((((x1 + y1) + (x2 + y2)) + ((x3 + y3) + (x4 + y4))) + (x5 + y5)) := by
  rw [← Nat.add_assoc (((x1 + x2) + (x3 + x4)) + x5) (((y1 + y2) + (y3 + y4))) y5]
  rw [Nat.add_right_comm ((x1 + x2) + (x3 + x4)) x5 ((y1 + y2) + (y3 + y4))]
  rw [Nat.add_assoc (((x1 + x2) + (x3 + x4)) + ((y1 + y2) + (y3 + y4))) x5 y5]
  rw [swap_mid (x1 + x2) (x3 + x4) (y1 + y2) (y3 + y4)]
  rw [swap_mid x1 x2 y1 y2, swap_mid x3 x4 y3 y4]

/-- Addition of two linear forms over the same basis. -/
theorem lin_add (a b e f g p q r s t p' q' r' s' t' : Nat) :
    lin a b e f g p q r s t + lin a b e f g p' q' r' s' t'
      = lin a b e f g (p + p') (q + q') (r + r') (s + s') (t + t') := by
  unfold lin
  rw [five_sum_add (p * a) (q * b) (r * e) (s * f) (t * g)
      (p' * a) (q' * b) (r' * e) (s' * f) (t' * g),
      ← add_mul_pure p p' a, ← add_mul_pure q q' b,
      ← add_mul_pure r r' e, ← add_mul_pure s s' f,
      ← add_mul_pure t t' g]

theorem c_step_one (n : Nat) :
    (c (n + 1)).1 = (c n).2.1 + (c n).2.2.1 := rfl

theorem c_step_two (n : Nat) :
    (c (n + 1)).2.1 = (c n).2.2.2.2 := rfl

theorem c_step_three (n : Nat) :
    (c (n + 1)).2.2.1 = (c n).1 + (c n).2.2.2.1 := rfl

theorem c_step_four (n : Nat) :
    (c (n + 1)).2.2.2.1 = (c n).2.1 + (c n).2.2.2.1 := rfl

theorem c_step_five (n : Nat) :
    (c (n + 1)).2.2.2.2 = (c n).1 := rfl

theorem c_one_one (n : Nat) :
    (c (n + 1)).1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 0 1 1 0 0 := by
  rw [c_step_one n]
  unfold lin
  rw [Nat.zero_mul, Nat.one_mul, Nat.one_mul, Nat.zero_mul, Nat.zero_mul,
      Nat.zero_add, Nat.add_zero, Nat.add_zero]

theorem c_one_two (n : Nat) :
    (c (n + 1)).2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 0 0 0 0 1 := by
  rw [c_step_two n]
  unfold lin
  rw [Nat.zero_mul, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.zero_add]

theorem c_one_three (n : Nat) :
    (c (n + 1)).2.2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 1 0 0 1 0 := by
  rw [c_step_three n]
  unfold lin
  rw [Nat.one_mul, Nat.zero_mul, Nat.zero_mul, Nat.one_mul, Nat.zero_mul,
      Nat.add_zero, Nat.zero_add, Nat.add_zero]

theorem c_one_four (n : Nat) :
    (c (n + 1)).2.2.2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 0 1 0 1 0 := by
  rw [c_step_four n]
  unfold lin
  rw [Nat.zero_mul, Nat.one_mul, Nat.zero_mul, Nat.one_mul, Nat.zero_mul]
  rw [Nat.zero_add (c n).2.1, Nat.zero_add (c n).2.2.2.1]
  rw [Nat.add_zero ((c n).2.1 + (c n).2.2.2.1)]

theorem c_one_five (n : Nat) :
    (c (n + 1)).2.2.2.2 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 1 0 0 0 0 := by
  rw [c_step_five n]
  unfold lin
  rw [Nat.one_mul, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul, Nat.add_zero]

theorem c_two_one (n : Nat) :
    (c (n + 2)).1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 1 0 0 1 1 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_one (n + 1), c_one_two n, c_one_three n, lin_add]

theorem c_two_two (n : Nat) :
    (c (n + 2)).2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 1 0 0 0 0 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_two (n + 1), c_one_five n]

theorem c_two_three (n : Nat) :
    (c (n + 2)).2.2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 0 2 1 1 0 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_three (n + 1), c_one_one n, c_one_four n, lin_add]

theorem c_two_four (n : Nat) :
    (c (n + 2)).2.2.2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 0 1 0 1 1 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_four (n + 1), c_one_two n, c_one_four n, lin_add]

theorem c_two_five (n : Nat) :
    (c (n + 2)).2.2.2.2 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 0 1 1 0 0 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_five (n + 1), c_one_one n]

theorem c_three_one (n : Nat) :
    (c (n + 3)).1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 1 2 1 1 0 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_one (n + 2), c_two_two n, c_two_three n, lin_add]

theorem c_three_two (n : Nat) :
    (c (n + 3)).2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 0 1 1 0 0 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_two (n + 2), c_two_five n]

theorem c_three_three (n : Nat) :
    (c (n + 3)).2.2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 1 1 0 2 2 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_three (n + 2), c_two_one n, c_two_four n, lin_add]

theorem c_three_four (n : Nat) :
    (c (n + 3)).2.2.2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 1 1 0 1 1 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_four (n + 2), c_two_two n, c_two_four n, lin_add]

theorem c_three_five (n : Nat) :
    (c (n + 3)).2.2.2.2 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 1 0 0 1 1 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_five (n + 2), c_two_one n]

theorem c_four_one (n : Nat) :
    (c (n + 4)).1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 1 2 1 2 2 := by
  rw [show n + 4 = (n + 3) + 1 by rfl]
  rw [c_step_one (n + 3), c_three_two n, c_three_three n, lin_add]

theorem c_four_two (n : Nat) :
    (c (n + 4)).2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 1 0 0 1 1 := by
  rw [show n + 4 = (n + 3) + 1 by rfl]
  rw [c_step_two (n + 3), c_three_five n]

theorem c_four_three (n : Nat) :
    (c (n + 4)).2.2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 2 3 1 2 1 := by
  rw [show n + 4 = (n + 3) + 1 by rfl]
  rw [c_step_three (n + 3), c_three_one n, c_three_four n, lin_add]

theorem c_four_four (n : Nat) :
    (c (n + 4)).2.2.2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 1 2 1 1 1 := by
  rw [show n + 4 = (n + 3) + 1 by rfl]
  rw [c_step_four (n + 3), c_three_two n, c_three_four n, lin_add]

theorem c_four_five (n : Nat) :
    (c (n + 4)).2.2.2.2 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 1 2 1 1 0 := by
  rw [show n + 4 = (n + 3) + 1 by rfl]
  rw [c_step_five (n + 3), c_three_one n]

theorem c_five_one (n : Nat) :
    (c (n + 5)).1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 3 3 1 3 2 := by
  rw [show n + 5 = (n + 4) + 1 by rfl]
  rw [c_step_one (n + 4), c_four_two n, c_four_three n, lin_add]

theorem Phi_base_lin (n : Nat) :
    Phi n =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 1 0 0 0 0 := by
  unfold Phi
  unfold lin
  rw [Nat.one_mul, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul, Nat.add_zero]

theorem Phi_one_lin (n : Nat) :
    Phi (n + 1) =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 0 1 1 0 0 := by
  unfold Phi
  rw [c_one_one n]

theorem Phi_three_lin (n : Nat) :
    Phi (n + 3) =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 1 2 1 1 0 := by
  unfold Phi
  rw [c_three_one n]

theorem Phi_four_lin (n : Nat) :
    Phi (n + 4) =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 1 2 1 2 2 := by
  unfold Phi
  rw [c_four_one n]

theorem Phi_five_lin (n : Nat) :
    Phi (n + 5) =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 3 3 1 3 2 := by
  unfold Phi
  rw [c_five_one n]

theorem flippability_mask_recurrence (n : Nat) :
    Phi (n + 5) + Phi (n + 1) = Phi (n + 4) + Phi (n + 3) + Phi n := by
  rw [Phi_five_lin n, Phi_one_lin n, Phi_four_lin n, Phi_three_lin n, Phi_base_lin n,
      lin_add, lin_add, lin_add]

end BEDC.Derived.Window6FlippabilityMaskRecurrence
