import BEDC.Derived.Window6FibonacciCount
import BEDC.Derived.Window6LucasCount

namespace BEDC.Derived.Window6LucasFibNormRelation

/--
Finite witness exponents for the Window6 Lucas-Fibonacci norm relation.
The window checks `0 <= n <= 25`; the doubling certificate therefore reads
Lucas values up to `L_50`.
-/
def normWitness : List Nat :=
  List.range 26

/--
The Window6 Lucas and Fibonacci counting sequences satisfy the classical
Lucas-Fibonacci norm identity
`L_n^2 - 5 F_n^2 = 4*(-1)^n` on the finite witness window.  Here `L_n` is
the cyclic Window6 count and `F_n` is the linear Fibonacci recurrence count;
the identity is the integer shadow of the norm of `phi^n` in `Z[phi]`.
-/
theorem lucas_fib_norm :
    normWitness.all (fun n =>
      ((BEDC.Derived.Window6Lucas.lucas n : Int)) ^ 2 -
            5 * ((BEDC.Derived.Window6Fibonacci.fib n : Int)) ^ 2 ==
          4 * (if n % 2 == 0 then (1 : Int) else (-1 : Int))) = true := by
  decide

/--
The same Window6 Lucas recurrence also satisfies the Lucas doubling identity
`L_(2n) = L_n^2 - 2*(-1)^n` on the finite witness window.
-/
theorem lucas_doubling :
    normWitness.all (fun n =>
      ((BEDC.Derived.Window6Lucas.lucas (2 * n) : Int)) ==
          ((BEDC.Derived.Window6Lucas.lucas n : Int)) ^ 2 -
            2 * (if n % 2 == 0 then (1 : Int) else (-1 : Int))) = true := by
  decide

example :
    ((BEDC.Derived.Window6Lucas.lucas 5 : Int)) ^ 2 -
        5 * ((BEDC.Derived.Window6Fibonacci.fib 5 : Int)) ^ 2 = -4 := by
  decide

example :
    ((BEDC.Derived.Window6Lucas.lucas 8 : Int)) ^ 2 -
        5 * ((BEDC.Derived.Window6Fibonacci.fib 8 : Int)) ^ 2 = 4 := by
  decide

end BEDC.Derived.Window6LucasFibNormRelation
