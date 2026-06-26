import BEDC.Derived.Window6FibonacciCount

namespace BEDC.Derived.Window6FibGcdStrongDivisibility

/--
Finite Window6 Fibonacci strong-divisibility witness grid.  The computation
checks the classical arithmetic law `gcd(F_m,F_n)=F_gcd(m,n)` on the small
Window6 counting range, where the same Fibonacci recurrence counts
`|X_m|=F_{m+2}`.  It also checks the forward divisibility corollary
`m | n => F_m | F_n` on the same grid.
-/
def gcdGrid : List (Nat × Nat) :=
  (List.range 13).flatMap (fun m => (List.range 13).map (fun n => (m, n)))

def divGrid : List (Nat × Nat) :=
  gcdGrid.filter (fun mn => mn.1 != 0 && mn.2 % mn.1 == 0)

/--
Direct finite computation of the Fibonacci strong divisibility equality
`gcd(F_m,F_n)=F_gcd(m,n)` on the Window6 witness grid.
-/
theorem fib_gcd_strong_divisibility :
    gcdGrid.all (fun mn =>
      Nat.gcd
          (BEDC.Derived.Window6Fibonacci.fib mn.1)
          (BEDC.Derived.Window6Fibonacci.fib mn.2) ==
        BEDC.Derived.Window6Fibonacci.fib (Nat.gcd mn.1 mn.2)) = true := by
  decide

/--
Direct finite computation of the forward corollary `m | n => F_m | F_n`
on the nonzero divisibility slice of the Window6 witness grid.  The
conclusion is recorded as the equivalent remainder check to keep the
certificate axiom-free.
-/
theorem fib_divisibility_witness :
    divGrid.all (fun mn =>
      BEDC.Derived.Window6Fibonacci.fib mn.2 %
          BEDC.Derived.Window6Fibonacci.fib mn.1 == 0) = true := by
  decide

example :
    Nat.gcd
        (BEDC.Derived.Window6Fibonacci.fib 6)
        (BEDC.Derived.Window6Fibonacci.fib 9) =
      BEDC.Derived.Window6Fibonacci.fib 3 := by
  decide

example :
    Nat.gcd
        (BEDC.Derived.Window6Fibonacci.fib 12)
        (BEDC.Derived.Window6Fibonacci.fib 18) =
      BEDC.Derived.Window6Fibonacci.fib 6 := by
  decide

end BEDC.Derived.Window6FibGcdStrongDivisibility
