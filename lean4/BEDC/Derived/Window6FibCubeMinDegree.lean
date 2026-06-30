namespace BEDC.Derived.Window6FibCubeMinDegree

/-- Degree of `w` given left-neighbor bit `prev`. A `true` always contributes
    one clearing move; a `false` contributes one setting move exactly when both
    adjacent bits are not `true`. -/
def degFrom : Bool → List Bool → Nat
  | _, [] => 0
  | prev, [a] => if a then 1 else (if prev then 0 else 1)
  | prev, (a :: b :: rest) =>
      (if a then 1 else (if prev || b then 0 else 1)) + degFrom a (b :: rest)

/-- Degree of a Fibonacci word, with no left neighbor at the start. -/
def deg (w : List Bool) : Nat := degFrom false w

/-- `noAdj prev w` says that `w` has no two adjacent `true` bits and the first
    bit is not jointly `true` with the external left neighbor `prev`. -/
def noAdj : Bool → List Bool → Bool
  | _, [] => true
  | prev, (a :: rest) => (!(prev && a)) && noAdj a rest

/-- Head-is-true indicator. -/
def headT : List Bool → Bool
  | [] => false
  | a :: _ => a

theorem deg_010 : deg [false, true, false] = 1 := rfl
theorem deg_00 : deg [false, false] = 2 := rfl
theorem deg_0 : deg [false] = 1 := rfl
theorem deg_periodic9 :
    deg [false, true, false, false, true, false, false, true, false] = 3 := rfl

theorem one_le_three : 1 ≤ 3 := Nat.succ_le_succ (Nat.zero_le 2)

theorem two_le_two : 2 ≤ 2 := Nat.le.refl

theorem two_le_three : 2 ≤ 3 :=
  Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 1))

theorem succ_le_mul_add_one {n d : Nat} (h : n ≤ 3 * d) :
    Nat.succ n ≤ 3 * (1 + d) := by
  rw [Nat.succ_eq_add_one]
  rw [Nat.mul_add, Nat.mul_one]
  rw [Nat.add_comm 3 (3 * d)]
  exact Nat.add_le_add h one_le_three

theorem succ_add_one_le_mul_add_one {n d : Nat} (h : n ≤ 3 * d + 1) :
    Nat.succ n + 1 ≤ 3 * (1 + d) := by
  rw [Nat.succ_eq_add_one]
  rw [Nat.mul_add, Nat.mul_one]
  rw [Nat.add_comm 3 (3 * d)]
  calc
    n + 1 + 1 ≤ (3 * d + 1) + 1 + 1 :=
      Nat.add_le_add (Nat.add_le_add h (Nat.le.refl)) (Nat.le.refl)
    _ = 3 * d + 3 := by
      rw [Nat.add_assoc, Nat.add_assoc]

theorem succ_le_add_one {n d : Nat} (h : n ≤ 3 * d) :
    Nat.succ n ≤ 3 * d + 1 := by
  rw [Nat.succ_eq_add_one]
  exact Nat.add_le_add h (Nat.le.refl)

theorem le_add_one_of_le {n d : Nat} (h : n ≤ 3 * d) :
    n ≤ 3 * d + 1 :=
  Nat.le_trans h (Nat.le_add_right (3 * d) 1)

theorem false_right_bonus (w : List Bool) :
    w.length ≤ w.length + (if headT w then 1 else 0) :=
  Nat.le_add_right w.length (if headT w then 1 else 0)

theorem head_bonus_false_false (rest : List Bool) :
    (if (!false && headT (false :: false :: rest)) = true then 1 else 0) = 0 := rfl

theorem head_bonus_false_true (rest : List Bool) :
    (if (!false && headT (false :: true :: rest)) = true then 1 else 0) = 0 := rfl

theorem head_bonus_true_false (rest : List Bool) :
    (if (!false && headT (true :: false :: rest)) = true then 1 else 0) = 1 := rfl

theorem head_bonus_prev_true_false_false (rest : List Bool) :
    (if (!true && headT (false :: false :: rest)) = true then 1 else 0) = 0 := rfl

theorem head_bonus_prev_true_false_true (rest : List Bool) :
    (if (!true && headT (false :: true :: rest)) = true then 1 else 0) = 0 := rfl

theorem prev_bonus_false : (if false = true then 1 else 0) = 0 := rfl

theorem prev_bonus_true : (if true = true then 1 else 0) = 1 := rfl

theorem deg_false_false_false (rest : List Bool) :
    degFrom false (false :: false :: rest) = 1 + degFrom false (false :: rest) := rfl

theorem deg_false_false_true (rest : List Bool) :
    degFrom false (false :: true :: rest) = degFrom false (true :: rest) := by
  rw [show degFrom false (false :: true :: rest) = 0 + degFrom false (true :: rest) by rfl]
  rw [Nat.zero_add]

theorem deg_false_true_false (rest : List Bool) :
    degFrom false (true :: false :: rest) = 1 + degFrom true (false :: rest) := rfl

theorem deg_true_false_false (rest : List Bool) :
    degFrom true (false :: false :: rest) = degFrom false (false :: rest) := by
  rw [show degFrom true (false :: false :: rest) = 0 + degFrom false (false :: rest) by rfl]
  rw [Nat.zero_add]

theorem deg_true_false_true (rest : List Bool) :
    degFrom true (false :: true :: rest) = degFrom false (true :: rest) := by
  rw [show degFrom true (false :: true :: rest) = 0 + degFrom false (true :: rest) by rfl]
  rw [Nat.zero_add]

theorem deg_invariant : ∀ (prev : Bool) (w : List Bool), noAdj prev w = true →
    w.length + (if (!prev) && headT w then 1 else 0)
      ≤ 3 * degFrom prev w + (if prev then 1 else 0)
  | false, [], _ => by
      exact Nat.le.refl
  | true, [], _ => by
      exact Nat.zero_le 1
  | false, [false], _ => by
      exact one_le_three
  | false, [true], _ => by
      exact two_le_three
  | true, [false], _ => by
      exact Nat.le.refl
  | true, [true], h => by
      cases h
  | false, false :: false :: rest, h => by
      have ih := deg_invariant false (false :: rest) h
      have ih2 : (false :: rest).length ≤ 3 * degFrom false (false :: rest) := ih
      rw [head_bonus_false_false rest, Nat.add_zero, prev_bonus_false, Nat.add_zero]
      rw [show (false :: false :: rest).length = Nat.succ (false :: rest).length by rfl]
      rw [deg_false_false_false rest]
      exact succ_le_mul_add_one ih2
  | false, false :: true :: rest, h => by
      have ih := deg_invariant false (true :: rest) h
      have ih2 : (true :: rest).length + 1 ≤ 3 * degFrom false (true :: rest) := ih
      rw [head_bonus_false_true rest, Nat.add_zero, prev_bonus_false, Nat.add_zero]
      rw [show (false :: true :: rest).length = Nat.succ (true :: rest).length by rfl]
      rw [deg_false_false_true rest]
      rw [Nat.succ_eq_add_one]
      exact ih2
  | false, true :: false :: rest, h => by
      have ih := deg_invariant true (false :: rest) h
      rw [head_bonus_true_false rest, prev_bonus_false, Nat.add_zero]
      rw [show (true :: false :: rest).length = Nat.succ (false :: rest).length by rfl]
      rw [deg_false_true_false rest]
      exact succ_add_one_le_mul_add_one ih
  | false, true :: true :: rest, h => by
      cases h
  | true, false :: false :: rest, h => by
      have ih := deg_invariant false (false :: rest) h
      have ih2 : (false :: rest).length ≤ 3 * degFrom false (false :: rest) := ih
      rw [head_bonus_prev_true_false_false rest, Nat.add_zero, prev_bonus_true]
      rw [show (false :: false :: rest).length = Nat.succ (false :: rest).length by rfl]
      rw [deg_true_false_false rest]
      exact succ_le_add_one ih2
  | true, false :: true :: rest, h => by
      have ih := deg_invariant false (true :: rest) h
      have ih2 : (true :: rest).length + 1 ≤ 3 * degFrom false (true :: rest) := ih
      rw [head_bonus_prev_true_false_true rest, Nat.add_zero, prev_bonus_true]
      rw [show (false :: true :: rest).length = Nat.succ (true :: rest).length by rfl]
      rw [deg_true_false_true rest]
      rw [Nat.succ_eq_add_one]
      exact le_add_one_of_le ih2
  | true, true :: false :: rest, h => by
      cases h
  | true, true :: true :: rest, h => by
      cases h

/-- Minimum-degree extremal bound for the Fibonacci cube: every Fibonacci word
    has `3 * deg(w) >= length(w)`. The periodic word `(010)^k` is sharp. -/
theorem fibcube_min_degree (w : List Bool) (h : noAdj false w = true) :
    w.length ≤ 3 * deg w := by
  have key := deg_invariant false w h
  unfold deg
  rw [prev_bonus_false, Nat.add_zero] at key
  exact Nat.le_trans (false_right_bonus w) key

end BEDC.Derived.Window6FibCubeMinDegree
