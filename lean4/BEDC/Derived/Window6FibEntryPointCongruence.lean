import BEDC.Derived.Window6FibonacciCount
import BEDC.Derived.Window6LucasCount

namespace BEDC.Derived.Window6FibEntryPointCongruence

/--
Fibonacci entry-point / Fermat congruence witness window for the Window6
Fibonacci and Lucas counting sequences.  For the nonramified primes in
`entryPrimes`, the residue class of `p mod 5` controls
`F_p ≡ (5/p) mod p`, while `L_p ≡ 1 mod p`; the ramified prime `p=5`
has `F_5 ≡ 0` and `L_5 ≡ 1`.  This is the sequence-level refinement of
the golden-split mod-p law, anchored in the Window6 counting sequences
`|X_m| = F_{m+2}` and cyclic count `L_m`.
-/
def entryPrimes : List Nat :=
  [2, 3, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59]

/--
For every nonramified prime in the finite witness window, direct computation
of the Window6 Fibonacci sequence gives `F_p ≡ (5/p) mod p`, with the
Legendre-symbol sign governed by `p mod 5`.
-/
theorem fib_entry_point_law :
    entryPrimes.all (fun p =>
      BEDC.Derived.Window6Fibonacci.fib p % p ==
        (if p % 5 == 1 || p % 5 == 4 then 1 else p - 1)) = true := by
  decide

/--
For every nonramified prime in the finite witness window, direct computation
of the Window6 Lucas sequence gives the Fermat congruence `L_p ≡ 1 mod p`.
-/
theorem lucas_fermat_congruence :
    entryPrimes.all (fun p =>
      BEDC.Derived.Window6Lucas.lucas p % p == 1 % p) = true := by
  decide

/-- The ramified prime `5` is its own Fibonacci entry-point: `F_5 ≡ 0 mod 5`. -/
theorem fib_five_entry_point :
    BEDC.Derived.Window6Fibonacci.fib 5 % 5 = 0 := by
  decide

/-- The Lucas Fermat congruence also holds at the ramified prime: `L_5 ≡ 1 mod 5`. -/
theorem lucas_five_mod :
    BEDC.Derived.Window6Lucas.lucas 5 % 5 = 1 := by
  decide

end BEDC.Derived.Window6FibEntryPointCongruence
