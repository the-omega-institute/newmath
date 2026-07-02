import BEDC.Derived.RHRoute.OCLSDPhaseAlgebra

/-
Canonical Fibonacci weight on the OCLSD PZG register (grounds the Fibonacci index).

Inspired by the innovation-geometry note "register norm² = log-time" (注记 7.6): the OCLSD
register `PZGRow` carries `(prime, Fibonacci-index)` atoms whose log-positions `F_k · log p`
were kept purely symbolic (OCLSDWeilGeometricAdapter).  This module supplies the arithmetic
that grounds that index: the per-prime Fibonacci weight of a register, and the fact that the
**Zeckendorf carry** `(p,k),(p,k+1) ↦ (p,k+2)` is an *isometry* of that weight
(`fib k + fib (k+1) = fib (k+2)`).  Hence the register's per-prime weight is the prime
valuation `v_p` read through its Zeckendorf digits, invariant under carry — the reason the
symbolic `Σ_{p,k} z_{p,k} F_k log p` collapses to `Σ_p v_p log p = log n = T` (the log-time,
命题 7.3 / cf. 定理 7.4 PZG completeness).

ζ-free, 0-axiom / propext-free (Nat recursion + `Nat.decEq`, no `Classical`).  Advances no
analytic gate: the `SpectralZeroIdentity` Hilbert–Pólya wall (OCLSDHamiltonian) is untouched.
-/

namespace BEDC.Derived.RHRoute.OCLSDRegisterWeight

open BEDC.Derived.RHRoute.OCLSDPhaseAlgebra

/-- Fibonacci numbers, `fib 0 = 0`, `fib 1 = 1`, `fib (k+2) = fib k + fib (k+1)`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | Nat.succ (Nat.succ n) => fib n + fib (Nat.succ n)

/-- The defining Zeckendorf-carry recurrence, definitionally. -/
theorem fib_carry (k : Nat) : fib (Nat.succ (Nat.succ k)) = fib k + fib (Nat.succ k) :=
  rfl

/-- Per-prime Fibonacci weight of a register: sum of `fib (fibIndex)` over the atoms whose
prime equals `target`.  For a Zeckendorf register this is the valuation `v_target`. -/
def primeFibWeight (target : Nat) : PZGRow → Nat
  | PZGRow.nil => 0
  | PZGRow.cons q k rest =>
      (if q = target then fib k else 0) + primeFibWeight target rest

@[simp] theorem primeFibWeight_nil (target : Nat) :
    primeFibWeight target PZGRow.nil = 0 := rfl

theorem primeFibWeight_cons (target q k : Nat) (rest : PZGRow) :
    primeFibWeight target (PZGRow.cons q k rest)
      = (if q = target then fib k else 0) + primeFibWeight target rest := rfl

/-- **Zeckendorf carry is an isometry of the register weight** (注记 7.6): replacing the
adjacent atoms `(p,k),(p,k+1)` by `(p,k+2)` preserves every per-prime weight, because
`fib k + fib (k+1) = fib (k+2)`.  The register's per-prime Fibonacci content is therefore
carry-invariant — a well-defined valuation, not an artifact of the digit representation. -/
theorem primeFibWeight_carry (target p k : Nat) (rest : PZGRow) :
    primeFibWeight target
        (PZGRow.cons p k (PZGRow.cons p (Nat.succ k) rest))
      = primeFibWeight target (PZGRow.cons p (Nat.succ (Nat.succ k)) rest) := by
  rw [primeFibWeight_cons, primeFibWeight_cons, primeFibWeight_cons]
  by_cases h : p = target
  · rw [if_pos h, if_pos h, if_pos h, fib_carry, Nat.add_assoc]
  · rw [if_neg h, if_neg h, if_neg h, Nat.zero_add, Nat.zero_add]

end BEDC.Derived.RHRoute.OCLSDRegisterWeight
