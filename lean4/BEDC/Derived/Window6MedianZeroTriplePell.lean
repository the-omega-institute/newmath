namespace BEDC.Derived.Window6MedianZeroTriplePell

/-
Median-zero ordered triples are counted as disjoint-support triples of binary
no-adjacent-ones words. Each coordinate carries one of four symbols:
`0` (all three words are zero), `A`, `B`, or `C`, with adjacent equal nonzero
symbols forbidden. The four transfer components count prefixes ending in those
symbols. The total count satisfies `T (m + 2) = 3 * T (m + 1) + T m`.
-/

/-- Transfer state `(eLast, aLast, bLast, cLast)` = counts of admissible prefixes
whose last symbol is `0`/empty, `A`, `B`, `C` respectively. -/
def c : Nat → Nat × Nat × Nat × Nat
  | 0 => (1, 0, 0, 0)
  | n + 1 =>
      ((c n).1 + (c n).2.1 + (c n).2.2.1 + (c n).2.2.2,
       (c n).1 + (c n).2.2.1 + (c n).2.2.2,
       (c n).1 + (c n).2.1 + (c n).2.2.2,
       (c n).1 + (c n).2.1 + (c n).2.2.1)

/-- Total median-zero triple count for length `m`. -/
def T (m : Nat) : Nat :=
  (c m).1 + (c m).2.1 + (c m).2.2.1 + (c m).2.2.2

theorem T_zero : T 0 = 1 := rfl
theorem T_one : T 1 = 4 := rfl
theorem T_two : T 2 = 13 := rfl
theorem T_three : T 3 = 43 := rfl
theorem T_four : T 4 = 142 := rfl

private theorem add_pull_left (a b c : Nat) :
    a + (b + c) = b + (a + c) := by
  rw [← Nat.add_assoc]
  rw [Nat.add_comm a b]
  rw [Nat.add_assoc]

private theorem three_mul_expand (x : Nat) :
    3 * x = (x + x) + x := by
  rw [Nat.succ_mul, Nat.succ_mul, Nat.succ_mul]
  rw [Nat.zero_mul, Nat.zero_add]

private theorem swap_after_five (p q r s t x y tail : Nat) :
    p + (q + (r + (s + (t + (x + (y + tail)))))) =
      p + (q + (r + (s + (t + (y + (x + tail)))))) := by
  rw [add_pull_left x y tail]

private theorem swap_after_six (p q r s t u x y tail : Nat) :
    p + (q + (r + (s + (t + (u + (x + (y + tail))))))) =
      p + (q + (r + (s + (t + (u + (y + (x + tail))))))) := by
  rw [add_pull_left x y tail]

private theorem swap_after_seven (p q r s t u v x y tail : Nat) :
    p + (q + (r + (s + (t + (u + (v + (x + (y + tail)))))))) =
      p + (q + (r + (s + (t + (u + (v + (y + (x + tail)))))))) := by
  rw [add_pull_left x y tail]

private theorem swap_after_nine (p q r s t u v w z x y tail : Nat) :
    p + (q + (r + (s + (t + (u + (v + (w + (z + (x + (y + tail)))))))))) =
      p + (q + (r + (s + (t + (u + (v + (w + (z + (y + (x + tail)))))))))) := by
  rw [add_pull_left x y tail]

private theorem swap_after_ten (p q r s t u v w z aa x y tail : Nat) :
    p + (q + (r + (s + (t + (u + (v + (w + (z + (aa + (x + (y + tail))))))))))) =
      p + (q + (r + (s + (t + (u + (v + (w + (z + (aa + (y + (x + tail))))))))))) := by
  rw [add_pull_left x y tail]

private theorem swap_after_eleven (p q r s t u v w z aa bb x y tail : Nat) :
    p + (q + (r + (s + (t + (u + (v + (w + (z + (aa + (bb + (x + (y + tail)))))))))))) =
      p + (q + (r + (s + (t + (u + (v + (w + (z + (aa + (bb + (y + (x + tail)))))))))))) := by
  rw [add_pull_left x y tail]

private theorem right_assoc_left (e a b cc : Nat) :
    (e + a + b + cc) + (e + b + cc) + (e + a + cc) + (e + a + b) =
      e + (a + (b + (cc + (e + (b + (cc + (e + (a + (cc + (e + (a + b))))))))))) := by
  rw [Nat.add_assoc]
  rw [Nat.add_assoc]
  rw [Nat.add_assoc]
  rw [Nat.add_assoc]
  rw [Nat.add_assoc]
  rw [Nat.add_assoc]
  rw [Nat.add_assoc]
  rw [Nat.add_assoc]
  rw [Nat.add_assoc]
  rw [Nat.add_assoc]

private theorem right_assoc_right (e a b cc : Nat) :
    ((e + a + b + cc) + (e + a + b + cc)) + (e + a + b + cc) + e =
      e + (a + (b + (cc + (e + (a + (b + (cc + (e + (a + (b + (cc + e))))))))))) := by
  rw [Nat.add_assoc]
  rw [Nat.add_assoc]
  rw [Nat.add_assoc]
  rw [Nat.add_assoc]
  rw [Nat.add_assoc]
  rw [Nat.add_assoc]
  rw [Nat.add_assoc]
  rw [Nat.add_assoc]
  rw [Nat.add_assoc]
  rw [Nat.add_assoc]
  rw [Nat.add_assoc]

private theorem triple_add_repack (e a b cc : Nat) :
    (e + a + b + cc) + (e + b + cc) + (e + a + cc) + (e + a + b)
      = ((e + a + b + cc) + (e + a + b + cc)) + (e + a + b + cc) + e := by
  calc
    (e + a + b + cc) + (e + b + cc) + (e + a + cc) + (e + a + b)
        = e + (a + (b + (cc + (e + (b + (cc + (e + (a + (cc + (e + (a + b))))))))))) :=
          right_assoc_left e a b cc
    _ = e + (a + (b + (cc + (e + (b + (cc + (a + (e + (cc + (e + (a + b))))))))))) :=
          swap_after_seven e a b cc e b cc e a (cc + (e + (a + b)))
    _ = e + (a + (b + (cc + (e + (b + (a + (cc + (e + (cc + (e + (a + b))))))))))) :=
          swap_after_six e a b cc e b cc a (e + (cc + (e + (a + b))))
    _ = e + (a + (b + (cc + (e + (a + (b + (cc + (e + (cc + (e + (a + b))))))))))) :=
          swap_after_five e a b cc e b a (cc + (e + (cc + (e + (a + b)))))
    _ = e + (a + (b + (cc + (e + (a + (b + (cc + (e + (cc + (a + (e + b))))))))))) :=
          swap_after_ten e a b cc e a b cc e cc e a b
    _ = e + (a + (b + (cc + (e + (a + (b + (cc + (e + (a + (cc + (e + b))))))))))) :=
          swap_after_nine e a b cc e a b cc e cc a (e + b)
    _ = e + (a + (b + (cc + (e + (a + (b + (cc + (e + (a + (cc + (b + e))))))))))) :=
          swap_after_eleven e a b cc e a b cc e a cc e b 0
    _ = e + (a + (b + (cc + (e + (a + (b + (cc + (e + (a + (b + (cc + e))))))))))) :=
          swap_after_ten e a b cc e a b cc e a cc b e
    _ = ((e + a + b + cc) + (e + a + b + cc)) + (e + a + b + cc) + e :=
          (right_assoc_right e a b cc).symm

/-- Pell-type recurrence for the median-zero ordered triple count. -/
theorem median_zero_triple_pell (m : Nat) : T (m + 2) = 3 * T (m + 1) + T m := by
  have hT2 : T (m + 2)
      = (c (m + 1)).1 + (c (m + 1)).2.1 + (c (m + 1)).2.2.1 +
          (c (m + 1)).2.2.2
        + ((c (m + 1)).1 + (c (m + 1)).2.2.1 + (c (m + 1)).2.2.2)
        + ((c (m + 1)).1 + (c (m + 1)).2.1 + (c (m + 1)).2.2.2)
        + ((c (m + 1)).1 + (c (m + 1)).2.1 + (c (m + 1)).2.2.1) := rfl
  have hT1 : T (m + 1)
      = (c m).1 + (c m).2.1 + (c m).2.2.1 + (c m).2.2.2
        + ((c m).1 + (c m).2.2.1 + (c m).2.2.2)
        + ((c m).1 + (c m).2.1 + (c m).2.2.2)
        + ((c m).1 + (c m).2.1 + (c m).2.2.1) := rfl
  have hcn1e : (c (m + 1)).1 =
      (c m).1 + (c m).2.1 + (c m).2.2.1 + (c m).2.2.2 := rfl
  have hcn1a : (c (m + 1)).2.1 =
      (c m).1 + (c m).2.2.1 + (c m).2.2.2 := rfl
  have hcn1b : (c (m + 1)).2.2.1 =
      (c m).1 + (c m).2.1 + (c m).2.2.2 := rfl
  have hcn1c : (c (m + 1)).2.2.2 =
      (c m).1 + (c m).2.1 + (c m).2.2.1 := rfl
  have hTm : T m = (c m).1 + (c m).2.1 + (c m).2.2.1 + (c m).2.2.2 := rfl
  rw [hT2, hT1, hTm, hcn1e, hcn1a, hcn1b, hcn1c, three_mul_expand]
  exact triple_add_repack
    ((c m).1 + (c m).2.1 + (c m).2.2.1 + (c m).2.2.2)
    ((c m).1 + (c m).2.2.1 + (c m).2.2.2)
    ((c m).1 + (c m).2.1 + (c m).2.2.2)
    ((c m).1 + (c m).2.1 + (c m).2.2.1)

end BEDC.Derived.Window6MedianZeroTriplePell

