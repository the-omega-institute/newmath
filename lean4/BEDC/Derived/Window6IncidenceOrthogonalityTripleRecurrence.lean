namespace BEDC.Derived.Window6IncidenceOrthogonalityTripleRecurrence

/-- Balanced five-term linear form over the current transfer state. -/
def lin (a b c d e p q r s t : Nat) : Nat := (((p * a + q * b) + (r * c + s * d)) + t * e)

/-- Five-state transfer for incidence-orthogonality triples in the Fibonacci cube. -/
def c : Nat → Nat × Nat × Nat × Nat × Nat
  | 0 => (1, 0, 0, 0, 0)
  | n + 1 =>
      let a := (c n).1
      let b := (c n).2.1
      let c2 := (c n).2.2.1
      let d := (c n).2.2.2.1
      let e := (c n).2.2.2.2
      (a + b + c2 + d + e, a + c2 + e, a + b, a, a + b)

def Y (m : Nat) : Nat :=
  ((((c m).1 + (c m).2.1) + (c m).2.2.1) + (c m).2.2.2.1) + (c m).2.2.2.2

theorem Y_zero : Y 0 = 1 := rfl
theorem Y_one : Y 1 = 5 := rfl
theorem Y_two : Y 2 = 13 := rfl
theorem Y_three : Y 3 = 43 := rfl
theorem Y_four : Y 4 = 129 := rfl

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
theorem lin_add (a b c d e p q r s t p' q' r' s' t' : Nat) :
    lin a b c d e p q r s t + lin a b c d e p' q' r' s' t'
      = lin a b c d e (p + p') (q + q') (r + r') (s + s') (t + t') := by
  unfold lin
  rw [five_sum_add (p * a) (q * b) (r * c) (s * d) (t * e)
      (p' * a) (q' * b) (r' * c) (s' * d) (t' * e),
      ← add_mul_pure p p' a, ← add_mul_pure q q' b,
      ← add_mul_pure r r' c, ← add_mul_pure s s' d,
      ← add_mul_pure t t' e]

/-- Scalar multiplication distributes over the linear form. -/
theorem lin_scale (a b c d e k p q r s t : Nat) :
    k * lin a b c d e p q r s t = lin a b c d e (k * p) (k * q) (k * r) (k * s) (k * t) := by
  unfold lin
  rw [Nat.mul_add k ((p * a + q * b) + (r * c + s * d)) (t * e),
      Nat.mul_add k (p * a + q * b) (r * c + s * d),
      Nat.mul_add k (p * a) (q * b), Nat.mul_add k (r * c) (s * d),
      ← mul_assoc_pure k p a, ← mul_assoc_pure k q b,
      ← mul_assoc_pure k r c, ← mul_assoc_pure k s d,
      ← mul_assoc_pure k t e]

/-- Multiplication by two distributes over the linear form. -/
theorem lin_two (a b c d e p q r s t : Nat) :
    2 * lin a b c d e p q r s t = lin a b c d e (2 * p) (2 * q) (2 * r) (2 * s) (2 * t) := by
  exact lin_scale a b c d e 2 p q r s t

theorem c_step_one (n : Nat) :
    (c (n + 1)).1 =
      (c n).1 + (c n).2.1 + (c n).2.2.1 + (c n).2.2.2.1 + (c n).2.2.2.2 := rfl

theorem c_step_two (n : Nat) :
    (c (n + 1)).2.1 = ((c n).1 + (c n).2.2.1) + (c n).2.2.2.2 := rfl

theorem c_step_three (n : Nat) :
    (c (n + 1)).2.2.1 = (c n).1 + (c n).2.1 := rfl

theorem c_step_four (n : Nat) :
    (c (n + 1)).2.2.2.1 = (c n).1 := rfl

theorem c_step_five (n : Nat) :
    (c (n + 1)).2.2.2.2 = (c n).1 + (c n).2.1 := rfl

theorem c_one_one (n : Nat) :
    (c (n + 1)).1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 1 1 1 1 1 := by
  rw [c_step_one n]
  unfold lin
  rw [Nat.one_mul, Nat.one_mul, Nat.one_mul, Nat.one_mul, Nat.one_mul,
      Nat.add_assoc ((c n).1 + (c n).2.1) (c n).2.2.1 (c n).2.2.2.1]

theorem c_one_two (n : Nat) :
    (c (n + 1)).2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 1 0 1 0 1 := by
  rw [c_step_two n]
  unfold lin
  rw [Nat.one_mul, Nat.zero_mul, Nat.one_mul, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.add_zero]

theorem c_one_three (n : Nat) :
    (c (n + 1)).2.2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 1 1 0 0 0 := by
  rw [c_step_three n]
  unfold lin
  rw [Nat.one_mul, Nat.one_mul, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul,
      Nat.add_zero]

theorem c_one_four (n : Nat) :
    (c (n + 1)).2.2.2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 1 0 0 0 0 := by
  rw [c_step_four n]
  unfold lin
  rw [Nat.one_mul, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul, Nat.add_zero]

theorem c_one_five (n : Nat) :
    (c (n + 1)).2.2.2.2 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 1 1 0 0 0 := by
  rw [c_step_five n]
  unfold lin
  rw [Nat.one_mul, Nat.one_mul, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul,
      Nat.add_zero]

theorem c_two_one (n : Nat) :
    (c (n + 2)).1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 5 3 2 1 2 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_one (n + 1), c_one_one n, c_one_two n, c_one_three n, c_one_four n,
      c_one_five n, lin_add, lin_add, lin_add, lin_add]

theorem c_two_two (n : Nat) :
    (c (n + 2)).2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 3 3 1 1 1 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_two (n + 1), c_one_one n, c_one_three n, c_one_five n,
      lin_add, lin_add]

theorem c_two_three (n : Nat) :
    (c (n + 2)).2.2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 2 1 2 1 2 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_three (n + 1), c_one_one n, c_one_two n, lin_add]

theorem c_two_four (n : Nat) :
    (c (n + 2)).2.2.2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 1 1 1 1 1 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_four (n + 1), c_one_one n]

theorem c_two_five (n : Nat) :
    (c (n + 2)).2.2.2.2 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 2 1 2 1 2 := by
  rw [show n + 2 = (n + 1) + 1 by rfl]
  rw [c_step_five (n + 1), c_one_one n, c_one_two n, lin_add]

theorem c_three_one (n : Nat) :
    (c (n + 3)).1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 13 9 8 5 8 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_one (n + 2), c_two_one n, c_two_two n, c_two_three n, c_two_four n,
      c_two_five n, lin_add, lin_add, lin_add, lin_add]

theorem c_three_two (n : Nat) :
    (c (n + 3)).2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 9 5 6 3 6 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_two (n + 2), c_two_one n, c_two_three n, c_two_five n,
      lin_add, lin_add]

theorem c_three_three (n : Nat) :
    (c (n + 3)).2.2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 8 6 3 2 3 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_three (n + 2), c_two_one n, c_two_two n, lin_add]

theorem c_three_four (n : Nat) :
    (c (n + 3)).2.2.2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 5 3 2 1 2 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_four (n + 2), c_two_one n]

theorem c_three_five (n : Nat) :
    (c (n + 3)).2.2.2.2 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 8 6 3 2 3 := by
  rw [show n + 3 = (n + 2) + 1 by rfl]
  rw [c_step_five (n + 2), c_two_one n, c_two_two n, lin_add]

theorem c_four_one (n : Nat) :
    (c (n + 4)).1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 43 29 22 13 22 := by
  rw [show n + 4 = (n + 3) + 1 by rfl]
  rw [c_step_one (n + 3), c_three_one n, c_three_two n, c_three_three n, c_three_four n,
      c_three_five n, lin_add, lin_add, lin_add, lin_add]

theorem c_four_two (n : Nat) :
    (c (n + 4)).2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 29 21 14 9 14 := by
  rw [show n + 4 = (n + 3) + 1 by rfl]
  rw [c_step_two (n + 3), c_three_one n, c_three_three n, c_three_five n,
      lin_add, lin_add]

theorem c_four_three (n : Nat) :
    (c (n + 4)).2.2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 22 14 14 8 14 := by
  rw [show n + 4 = (n + 3) + 1 by rfl]
  rw [c_step_three (n + 3), c_three_one n, c_three_two n, lin_add]

theorem c_four_four (n : Nat) :
    (c (n + 4)).2.2.2.1 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 13 9 8 5 8 := by
  rw [show n + 4 = (n + 3) + 1 by rfl]
  rw [c_step_four (n + 3), c_three_one n]

theorem c_four_five (n : Nat) :
    (c (n + 4)).2.2.2.2 =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 22 14 14 8 14 := by
  rw [show n + 4 = (n + 3) + 1 by rfl]
  rw [c_step_five (n + 3), c_three_one n, c_three_two n, lin_add]

theorem Y_base_lin (n : Nat) :
    Y n =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 1 1 1 1 1 := by
  unfold Y
  unfold lin
  rw [Nat.one_mul, Nat.one_mul, Nat.one_mul, Nat.one_mul, Nat.one_mul,
      Nat.add_assoc ((c n).1 + (c n).2.1) (c n).2.2.1 (c n).2.2.2.1]

theorem Y_one_lin (n : Nat) :
    Y (n + 1) =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 5 3 2 1 2 := by
  unfold Y
  rw [c_one_one n, c_one_two n, c_one_three n, c_one_four n, c_one_five n,
      lin_add, lin_add, lin_add, lin_add]

theorem Y_two_lin (n : Nat) :
    Y (n + 2) =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 13 9 8 5 8 := by
  unfold Y
  rw [c_two_one n, c_two_two n, c_two_three n, c_two_four n, c_two_five n,
      lin_add, lin_add, lin_add, lin_add]

theorem Y_three_lin (n : Nat) :
    Y (n + 3) =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 43 29 22 13 22 := by
  unfold Y
  rw [c_three_one n, c_three_two n, c_three_three n, c_three_four n, c_three_five n,
      lin_add, lin_add, lin_add, lin_add]

theorem Y_four_lin (n : Nat) :
    Y (n + 4) =
      lin (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 129 87 72 43 72 := by
  unfold Y
  rw [c_four_one n, c_four_two n, c_four_three n, c_four_four n, c_four_five n,
      lin_add, lin_add, lin_add, lin_add]

theorem incidence_orthogonality_triple_recurrence (n : Nat) :
    Y (n + 4) + 2 * Y n = Y (n + 3) + 6 * Y (n + 2) + 2 * Y (n + 1) := by
  rw [Y_four_lin n, Y_base_lin n, Y_three_lin n, Y_two_lin n, Y_one_lin n,
      lin_two (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 1 1 1 1 1,
      lin_add,
      lin_scale (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 6 13 9 8 5 8,
      lin_two (c n).1 (c n).2.1 (c n).2.2.1 (c n).2.2.2.1 (c n).2.2.2.2 5 3 2 1 2,
      lin_add, lin_add]

end BEDC.Derived.Window6IncidenceOrthogonalityTripleRecurrence
