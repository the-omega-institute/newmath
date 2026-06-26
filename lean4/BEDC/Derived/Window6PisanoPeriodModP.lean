/-!
Window6 Pisano period mod-p divisibility law.

The Pisano period `π(m)` is the least positive return time of the
Fibonacci state `(F_k mod m, F_{k+1} mod m)` to `(0,1)`.  This module
computes the period by a fuel-bounded forward recurrence on residues.
For the finite prime witness window, direct computation records the
classical mod-p divisibility law governed by `p mod 5`: split primes
`p % 5 in {1,4}` have `π(p) | p-1`, inert primes `p % 5 in {2,3}` have
`π(p) | 2*(p+1)`, and the ramified prime has `π(5)=20`.

Window6 Pisano 周期 `π(m)` 是 Fibonacci residue 状态
`(F_k mod m, F_{k+1} mod m)` 首次正向回到 `(0,1)` 的时间。本模块
用 fuel-bounded residue 递推直接搜索周期，并在有限素数 witness
窗口中记录由 `p mod 5` 支配的经典整除律：分裂素数满足 `π(p) | p-1`，
惰性素数满足 `π(p) | 2*(p+1)`，分歧素数满足 `π(5)=20`。这是
golden-split / entry-point mod-p 弧的周期层。
-/

namespace BEDC.Derived.Window6PisanoPeriodModP

/--
Fuel-bounded forward search for the Pisano period.  The state `(a,b,k)`
represents `(F_k mod m, F_{k+1} mod m, k)`, starting from `(0,1,0)`;
the first positive return to `(0,1)` is returned.
-/
def pisanoAux (m : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _ => 0
  | Nat.succ fuel, a, b, k =>
      if a == 0 && b == 1 && decide (k > 0) then k
      else pisanoAux m fuel b ((a + b) % m) (k + 1)

/-- Fuel-bounded Pisano period search with the standard `6*m+1` witness fuel. -/
def pisanoPeriod (m : Nat) : Nat :=
  pisanoAux m (6 * m + 1) 0 1 0

/-- Named Pisano-period examples computed by the residue-state search. -/
theorem pisano_values :
    ([(2, 3), (3, 8), (4, 6), (5, 20), (7, 16), (10, 60), (11, 10), (12, 24)] :
      List (Nat × Nat)).all (fun mp => pisanoPeriod mp.1 == mp.2) = true := by
  decide

def primeWitnesses : List Nat :=
  [2, 3, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]

def primePisanoDivisibilityWitness (p : Nat) : Bool :=
  if p % 5 == 1 || p % 5 == 4 then
    (p - 1) % pisanoPeriod p == 0
  else if p % 5 == 2 || p % 5 == 3 then
    (2 * (p + 1)) % pisanoPeriod p == 0
  else
    false

/--
For the finite nonramified prime witness window, the directly searched
Pisano periods satisfy the classical divisibility law controlled by
`p mod 5`.
-/
theorem pisano_prime_modp_law :
    primeWitnesses.all primePisanoDivisibilityWitness = true := by
  decide

/-- The ramified prime has Pisano period `20`. -/
theorem pisano_five :
    pisanoPeriod 5 = 20 := by
  decide

end BEDC.Derived.Window6PisanoPeriodModP
