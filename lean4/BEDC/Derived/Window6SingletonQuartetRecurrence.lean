namespace BEDC.Derived.Window6SingletonQuartetRecurrence

/-- Balanced five-term linear form over the current transfer state. -/
def lin (a b e f g p q r s t : Nat) : Nat := (((p * a + q * b) + (r * e + s * f)) + t * g)

/-- Nonnegative five-state transfer for the singleton-mask quartet count. -/
def c : Nat → Nat × Nat × Nat × Nat × Nat
  | 0 => (1, 1, 1, 1, 1)
  | n + 1 =>
      let a := (c n).1
      let b := (c n).2.1
      let e := (c n).2.2.1
      let f := (c n).2.2.2.1
      let g := (c n).2.2.2.2
      (((a + 4 * b) + (6 * e + 4 * f)) + g,
        a + (3 * e + f), (a + 2 * b) + e, a + b, a)

def B (m : Nat) : Nat := (c m).1

theorem B_zero : B 0 = 1 := rfl
theorem B_one : B 1 = 16 := rfl
theorem B_two : B 2 = 69 := rfl
theorem B_three : B 3 = 469 := rfl
theorem B_four : B 4 = 2608 := rfl
theorem B_five : B 5 = 15781 := rfl

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

/-- Scalar multiplication distributes over the linear form. -/
theorem lin_scale (a b e f g k p q r s t : Nat) :
    k * lin a b e f g p q r s t = lin a b e f g (k * p) (k * q) (k * r) (k * s) (k * t) := by
  unfold lin
  rw [Nat.mul_add k ((p * a + q * b) + (r * e + s * f)) (t * g),
      Nat.mul_add k (p * a + q * b) (r * e + s * f),
      Nat.mul_add k (p * a) (q * b), Nat.mul_add k (r * e) (s * f),
      ← mul_assoc_pure k p a, ← mul_assoc_pure k q b,
      ← mul_assoc_pure k r e, ← mul_assoc_pure k s f,
      ← mul_assoc_pure k t g]

theorem c_step_one (n : Nat) :
    (c (n + 1)).1 =
      (((c n).1 + 4 * (c n).2.1) + (6 * (c n).2.2.1 + 4 * (c n).2.2.2.1)) +
        (c n).2.2.2.2 := rfl

theorem c_step_two (n : Nat) :
    (c (n + 1)).2.1 = (c n).1 + (3 * (c n).2.2.1 + (c n).2.2.2.1) := rfl

theorem c_step_three (n : Nat) :
    (c (n + 1)).2.2.1 = ((c n).1 + 2 * (c n).2.1) + (c n).2.2.1 := rfl

theorem c_step_four (n : Nat) :
    (c (n + 1)).2.2.2.1 = (c n).1 + (c n).2.1 := rfl

theorem c_step_five (n : Nat) :
    (c (n + 1)).2.2.2.2 = (c n).1 := rfl

theorem c_one_one (n : Nat) :
    (c (n + 1)).1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 1 4 6 4 1 := by
  rw [c_step_one n]
  unfold lin
  rw [Nat.one_mul, Nat.one_mul]

theorem c_one_two (n : Nat) :
    (c (n + 1)).2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 1 0 3 1 0 := by
  rw [c_step_two n]
  unfold lin
  rw [Nat.one_mul, Nat.zero_mul, Nat.one_mul, Nat.zero_mul,
      Nat.add_zero, Nat.add_zero]

theorem c_one_three (n : Nat) :
    (c (n + 1)).2.2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 1 2 1 0 0 := by
  rw [c_step_three n]
  unfold lin
  rw [Nat.one_mul, Nat.one_mul, Nat.zero_mul, Nat.zero_mul,
      Nat.add_zero, Nat.add_zero]

theorem c_one_four (n : Nat) :
    (c (n + 1)).2.2.2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 1 1 0 0 0 := by
  rw [c_step_four n]
  unfold lin
  rw [Nat.one_mul, Nat.one_mul, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul,
      Nat.zero_add, Nat.add_zero]

theorem c_one_five (n : Nat) :
    (c (n + 1)).2.2.2.2 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 1 0 0 0 0 := by
  rw [c_step_five n]
  unfold lin
  rw [Nat.one_mul, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul, Nat.add_zero]

theorem c_two_one (n : Nat) :
    (c (n + 2)).1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 16 20 24 8 1 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_one (n + 1), c_one_one n, c_one_two n, c_one_three n, c_one_four n,
      c_one_five n,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 4 1 0 3 1 0,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 6 1 2 1 0 0,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 4 1 1 0 0 0,
      lin_add, lin_add, lin_add, lin_add]

theorem c_two_two (n : Nat) :
    (c (n + 2)).2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 5 11 9 4 1 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_two (n + 1), c_one_one n, c_one_three n, c_one_four n,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 3 1 2 1 0 0,
      lin_add, lin_add]

theorem c_two_three (n : Nat) :
    (c (n + 2)).2.2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 4 6 13 6 1 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_three (n + 1), c_one_one n, c_one_two n, c_one_three n,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 2 1 0 3 1 0,
      lin_add, lin_add]

theorem c_two_four (n : Nat) :
    (c (n + 2)).2.2.2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 2 4 9 5 1 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_four (n + 1), c_one_one n, c_one_two n, lin_add]

theorem c_two_five (n : Nat) :
    (c (n + 2)).2.2.2.2 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 1 4 6 4 1 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_five (n + 1), c_one_one n]

theorem c_three_one (n : Nat) :
    (c (n + 3)).1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 69 120 180 84 16 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_one (n + 2), c_two_one n, c_two_two n, c_two_three n, c_two_four n,
      c_two_five n,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 4 5 11 9 4 1,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 6 4 6 13 6 1,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 4 2 4 9 5 1,
      lin_add, lin_add, lin_add, lin_add]

theorem c_three_two (n : Nat) :
    (c (n + 3)).2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 30 42 72 31 5 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_two (n + 2), c_two_one n, c_two_three n, c_two_four n,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 3 4 6 13 6 1,
      lin_add, lin_add]

theorem c_three_three (n : Nat) :
    (c (n + 3)).2.2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 30 48 55 22 4 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_three (n + 2), c_two_one n, c_two_two n, c_two_three n,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 2 5 11 9 4 1,
      lin_add, lin_add]

theorem c_three_four (n : Nat) :
    (c (n + 3)).2.2.2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 21 31 33 12 2 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_four (n + 2), c_two_one n, c_two_two n, lin_add]

theorem c_three_five (n : Nat) :
    (c (n + 3)).2.2.2.2 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 16 20 24 8 1 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_five (n + 2), c_two_one n]

theorem c_four_one (n : Nat) :
    (c (n + 4)).1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 469 720 954 396 69 := by
  rw [show n + 4 = (n + 3) + 1 by rfl]
  rw [c_step_one (n + 3), c_three_one n, c_three_two n, c_three_three n, c_three_four n,
      c_three_five n,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 4 30 42 72 31 5,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 6 30 48 55 22 4,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 4 21 31 33 12 2,
      lin_add, lin_add, lin_add, lin_add]

theorem c_four_two (n : Nat) :
    (c (n + 4)).2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 180 295 378 162 30 := by
  rw [show n + 4 = (n + 3) + 1 by rfl]
  rw [c_step_two (n + 3), c_three_one n, c_three_three n, c_three_four n,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 3 30 48 55 22 4,
      lin_add, lin_add]

theorem c_four_three (n : Nat) :
    (c (n + 4)).2.2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 159 252 379 168 30 := by
  rw [show n + 4 = (n + 3) + 1 by rfl]
  rw [c_step_three (n + 3), c_three_one n, c_three_two n, c_three_three n,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 2 30 42 72 31 5,
      lin_add, lin_add]

theorem c_four_four (n : Nat) :
    (c (n + 4)).2.2.2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 99 162 252 115 21 := by
  rw [show n + 4 = (n + 3) + 1 by rfl]
  rw [c_step_four (n + 3), c_three_one n, c_three_two n, lin_add]

theorem c_four_five (n : Nat) :
    (c (n + 4)).2.2.2.2 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 69 120 180 84 16 := by
  rw [show n + 4 = (n + 3) + 1 by rfl]
  rw [c_step_five (n + 3), c_three_one n]

theorem c_five_one (n : Nat) :
    (c (n + 5)).1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 2608 4180 5928 2596 469 := by
  rw [show n + 5 = (n + 4) + 1 by rfl]
  rw [c_step_one (n + 4), c_four_one n, c_four_two n, c_four_three n, c_four_four n,
      c_four_five n,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 4 180 295 378 162 30,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 6 159 252 379 168 30,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 4 99 162 252 115 21,
      lin_add, lin_add, lin_add, lin_add]

theorem B_base_lin (n : Nat) :
    B n =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 1 0 0 0 0 := by
  unfold B
  unfold lin
  rw [Nat.one_mul, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul, Nat.add_zero]

theorem B_one_lin (n : Nat) :
    B (n + 1) =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 1 4 6 4 1 := by
  unfold B
  rw [c_one_one n]

theorem B_two_lin (n : Nat) :
    B (n + 2) =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 16 20 24 8 1 := by
  unfold B
  rw [c_two_one n]

theorem B_three_lin (n : Nat) :
    B (n + 3) =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 69 120 180 84 16 := by
  unfold B
  rw [c_three_one n]

theorem B_four_lin (n : Nat) :
    B (n + 4) =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 469 720 954 396 69 := by
  unfold B
  rw [c_four_one n]

theorem B_five_lin (n : Nat) :
    B (n + 5) =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 2608 4180 5928 2596 469 := by
  unfold B
  rw [c_five_one n]

theorem singleton_quartet_recurrence (n : Nat) :
    B (n + 5) + 20 * B (n + 1) =
      2 * B (n + 4) + 21 * B (n + 3) + 15 * B (n + 2) + B n := by
  rw [B_five_lin n, B_one_lin n, B_four_lin n, B_three_lin n, B_two_lin n, B_base_lin n,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 20 1 4 6 4 1,
      lin_add,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 2 469 720 954 396 69,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 21 69 120 180 84 16,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 15 16 20 24 8 1,
      lin_add, lin_add, lin_add]

end BEDC.Derived.Window6SingletonQuartetRecurrence
