namespace BEDC.Derived.Window6DisjointPairPell

/-
Disjoint-support ordered pairs (u, v) of length-m no-adjacent-ones words, counted
by the three-state transfer (last symbol 0 / A=only u / B=only v) over the alphabet
{0, A, B} forbidding adjacent AA and adjacent BB. The count D m satisfies the Pell
recurrence D (m+2) = 2 * D (m+1) + D m. Proof is mathlib-free and axiom-free:
structural recursion makes every transfer equation rfl, induction proves the A=B
symmetry, and omega closes the linear arithmetic. No simp (which would leak propext).
-/

/-- Transfer state `(eLast, aLast, bLast)` = counts of admissible prefixes whose last
symbol is `0`/empty, `A`, `B` respectively. -/
def c : Nat → Nat × Nat × Nat
  | 0 => (1, 0, 0)
  | n + 1 =>
      ((c n).1 + (c n).2.1 + (c n).2.2,
       (c n).1 + (c n).2.2,
       (c n).1 + (c n).2.1)

/-- Total disjoint-support pair count for length `m`. -/
def D (m : Nat) : Nat :=
  (c m).1 + (c m).2.1 + (c m).2.2

theorem D_zero : D 0 = 1 := rfl
theorem D_one : D 1 = 3 := rfl
theorem D_two : D 2 = 7 := rfl
theorem D_three : D 3 = 17 := rfl

/-- The A-terminal and B-terminal counts coincide (reversal symmetry of the language). -/
theorem aLast_eq_bLast (n : Nat) : (c n).2.1 = (c n).2.2 := by
  induction n with
  | zero => rfl
  | succ k ih =>
      have e1 : (c (k + 1)).2.1 = (c k).1 + (c k).2.2 := rfl
      have e2 : (c (k + 1)).2.2 = (c k).1 + (c k).2.1 := rfl
      rw [e1, e2, ih]

/-- Pell recurrence for the disjoint-support pair count. Holds as a pure additive
identity (both sides equal `7P + 5Q + 5R` in the components `P,Q,R` of `c n`), so it
closes by associativity-commutativity without omega (which would leak propext). -/
theorem disjoint_pair_pell (n : Nat) : D (n + 2) = 2 * D (n + 1) + D n := by
  -- Unfold D at n+2, n+1, n to component counts; every step below is rfl.
  have hD2 : D (n + 2)
      = (c (n + 1)).1 + (c (n + 1)).2.1 + (c (n + 1)).2.2
        + ((c (n + 1)).1 + (c (n + 1)).2.2)
        + ((c (n + 1)).1 + (c (n + 1)).2.1) := rfl
  have hD1 : D (n + 1) = (c n).1 + (c n).2.1 + (c n).2.2
        + ((c n).1 + (c n).2.2) + ((c n).1 + (c n).2.1) := rfl
  have hcn1e : (c (n + 1)).1 = (c n).1 + (c n).2.1 + (c n).2.2 := rfl
  have hcn1a : (c (n + 1)).2.1 = (c n).1 + (c n).2.2 := rfl
  have hcn1b : (c (n + 1)).2.2 = (c n).1 + (c n).2.1 := rfl
  have hDn : D n = (c n).1 + (c n).2.1 + (c n).2.2 := rfl
  rw [hD2, hD1, hDn, hcn1e, hcn1a, hcn1b, Nat.two_mul]
  have hPair : ∀ x y z : Nat, (x + z) + (x + y) = x + y + z + x := by
    intro x y z
    calc
      (x + z) + (x + y) = x + (z + (x + y)) := by rw [Nat.add_assoc]
      _ = x + ((x + y) + z) := by rw [Nat.add_comm z (x + y)]
      _ = ((x + y) + z) + x := by rw [Nat.add_comm x ((x + y) + z)]
  have hReassocTail : ∀ a b cc d : Nat, a + b + (cc + d) = a + b + cc + d := by
    intro a b cc d
    rw [← Nat.add_assoc (a + b) cc d]
  have hPellAdd :
      ∀ x y z : Nat,
        x + y + z + (x + z) + (x + y) = x + y + z + (x + y + z) + x := by
    intro x y z
    calc
      x + y + z + (x + z) + (x + y)
          = x + y + z + ((x + z) + (x + y)) := by
            rw [Nat.add_assoc (x + y + z) (x + z) (x + y)]
      _ = x + y + z + (x + y + z + x) := by rw [hPair x y z]
      _ = x + y + z + (x + y + z) + x := by
            rw [hReassocTail (x + y) z (x + y + z) x]
  exact hPellAdd
    ((c n).1 + (c n).2.1 + (c n).2.2)
    ((c n).1 + (c n).2.2)
    ((c n).1 + (c n).2.1)

theorem disjoint_pair_pell_initial : D 0 = 1 ∧ D 1 = 3 := ⟨D_zero, D_one⟩

end BEDC.Derived.Window6DisjointPairPell
