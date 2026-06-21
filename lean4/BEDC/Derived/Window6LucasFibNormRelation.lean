import BEDC.Derived.Window6FibonacciCount
import BEDC.Derived.Window6LucasCount
import BEDC.Derived.Window6TransferMatrix

namespace BEDC.Derived.Window6LucasFibNormRelation

private theorem add_mul_pure (a b c : Nat) :
    (a + b) * c = a * c + b * c := by
  induction c with
  | zero =>
      rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | succ c ih =>
      calc
        (a + b) * Nat.succ c =
            (a + b) * c + (a + b) := Nat.mul_succ (a + b) c
        _ = (a * c + b * c) + (a + b) :=
          congrArg (fun x => x + (a + b)) ih
        _ = a * c + (b * c + (a + b)) :=
          Nat.add_assoc (a * c) (b * c) (a + b)
        _ = a * c + ((b * c + a) + b) :=
          congrArg (fun x => a * c + x) (Nat.add_assoc (b * c) a b).symm
        _ = a * c + ((a + b * c) + b) :=
          congrArg (fun x => a * c + (x + b)) (Nat.add_comm (b * c) a)
        _ = a * c + (a + (b * c + b)) :=
          congrArg (fun x => a * c + x) (Nat.add_assoc a (b * c) b)
        _ = (a * c + a) + (b * c + b) :=
          (Nat.add_assoc (a * c) a (b * c + b)).symm
        _ = a * Nat.succ c + (b * c + b) :=
          congrArg (fun x => x + (b * c + b)) (Nat.mul_succ a c).symm
        _ = a * Nat.succ c + b * Nat.succ c :=
          congrArg (fun x => a * Nat.succ c + x) (Nat.mul_succ b c).symm

private theorem add_pull_left (a b c : Nat) :
    a + (b + c) = b + (a + c) := by
  rw [← Nat.add_assoc]
  rw [Nat.add_comm a b]
  rw [Nat.add_assoc]

private theorem add_move_head (tail x y z : Nat) :
    x + (y + (y + (y + (z + (z + (y + (z + (z + tail)))))))) =
      y + (y + (y + (z + (z + (y + (z + (z + (x + tail)))))))) := by
  rw [add_pull_left x y]
  rw [add_pull_left x y]
  rw [add_pull_left x y]
  rw [add_pull_left x z]
  rw [add_pull_left x z]
  rw [add_pull_left x y]
  rw [add_pull_left x z]
  rw [add_pull_left x z]

private theorem add_move_prefix (tail y z : Nat) :
    y + (y + (y + (z + (z + (y + (z + (z + tail))))))) =
      y + (z + (y + (z + (y + (z + (y + (z + tail))))))) := by
  calc
    y + (y + (y + (z + (z + (y + (z + (z + tail))))))) =
        y + (y + (z + (y + (z + (y + (z + (z + tail))))))) := by
      conv =>
        lhs
        congr
        · skip
        · rw [add_pull_left y z]
    _ = y + (z + (y + (y + (z + (y + (z + (z + tail))))))) := by
      conv =>
        lhs
        congr
        · skip
        · rw [add_pull_left y z]
    _ = y + (z + (y + (z + (y + (y + (z + (z + tail))))))) := by
      conv =>
        lhs
        congr
        · skip
        · congr
          · skip
          · congr
            · skip
            · rw [add_pull_left y z]
    _ = y + (z + (y + (z + (y + (z + (y + (z + tail))))))) := by
      conv =>
        lhs
        congr
        · skip
        · congr
          · skip
          · congr
            · skip
            · congr
              · skip
              · congr
                · skip
                · rw [add_pull_left y z]

private theorem four_mul_expand (x : Nat) :
    4 * x = x + x + x + x := by
  change Nat.succ (Nat.succ (Nat.succ (Nat.succ 0))) * x = x + x + x + x
  rw [Nat.succ_mul, Nat.succ_mul, Nat.succ_mul, Nat.succ_mul]
  rw [Nat.zero_mul, Nat.zero_add]

private theorem five_mul_expand (x : Nat) :
    5 * x = x + x + x + x + x := by
  change Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ 0)))) * x =
    x + x + x + x + x
  rw [Nat.succ_mul, Nat.succ_mul, Nat.succ_mul, Nat.succ_mul, Nat.succ_mul]
  rw [Nat.zero_mul, Nat.zero_add]

private theorem add_repack (x y z : Nat) :
    x + y + y + (y + z + z) + (y + z + z) + 4 * x =
      4 * (y + z) + 5 * x := by
  rw [four_mul_expand x, four_mul_expand (y + z), five_mul_expand x]
  repeat rw [Nat.add_assoc]
  rw [add_move_head (x + (x + (x + x))) x y z]
  exact add_move_prefix (x + (x + (x + (x + x)))) y z

private theorem norm_cross_nat (a b : Nat) :
    (b + a + a) * (b + a + a) + 4 * (b * b) =
      4 * ((b + a) * a) + 5 * (b * b) := by
  rw [add_mul_pure (b + a) a (b + a + a)]
  rw [add_mul_pure b a (b + a + a)]
  rw [Nat.mul_add b (b + a) a]
  rw [Nat.mul_add b b a]
  rw [Nat.mul_add a (b + a) a]
  rw [Nat.mul_add a b a]
  rw [Nat.mul_comm a b]
  rw [add_mul_pure b a a]
  exact add_repack (b * b) (b * a) (a * a)

private theorem subNatNat_succ_succ (m n : Nat) :
    Int.subNatNat (m + 1) (n + 1) = Int.subNatNat m n := by
  unfold Int.subNatNat
  rw [Nat.succ_sub_succ_eq_sub]
  rw [Nat.succ_sub_succ_eq_sub]

private theorem subNatNat_add_add_right (m n k : Nat) :
    Int.subNatNat (m + k) (n + k) = Int.subNatNat m n := by
  induction k with
  | zero =>
      rw [Nat.add_zero]
      rw [Nat.add_zero]
  | succ k ih =>
      change Int.subNatNat ((m + k) + 1) ((n + k) + 1) = Int.subNatNat m n
      rw [subNatNat_succ_succ]
      exact ih

private theorem subNatNat_cross_eq (m n p q : Nat)
    (h : m + q = p + n) :
    Int.subNatNat m n = Int.subNatNat p q := by
  rw [← subNatNat_add_add_right m n q]
  rw [h]
  rw [Nat.add_comm n q]
  exact subNatNat_add_add_right p q n

private theorem subNatNat_zero_right (m : Nat) :
    Int.subNatNat (m + 1) 0 = Int.ofNat (m + 1) := by
  unfold Int.subNatNat
  rw [Nat.zero_sub]
  rw [Nat.sub_zero]

private theorem ofNat_sub_ofNat_eq_subNatNat : ∀ (m n : Nat),
    ((m : Nat) : Int) - ((n : Nat) : Int) = Int.subNatNat m n
  | 0, 0 => rfl
  | 0, n + 1 => rfl
  | m + 1, 0 => by
      change Int.ofNat (m + 1) = Int.subNatNat (m + 1) 0
      exact (subNatNat_zero_right m).symm
  | _ + 1, _ + 1 => by
      rfl

private theorem nat_pow_two (m : Nat) :
    m ^ 2 = m * m := by
  rw [show (2 : Nat) = Nat.succ 1 by rfl]
  rw [Nat.pow_succ]
  rw [show (1 : Nat) = Nat.succ 0 by rfl]
  rw [Nat.pow_succ]
  rw [Nat.pow_zero]
  rw [Nat.one_mul]

private theorem int_sq_nat (m : Nat) :
    ((m : Nat) : Int) ^ 2 = ((m * m : Nat) : Int) := by
  change Int.ofNat (m ^ 2) = Int.ofNat (m * m)
  exact congrArg Int.ofNat (nat_pow_two m)

private theorem lhs_to_sub (u b : Nat) :
    ((u : Int)) ^ 2 - 5 * ((b : Int)) ^ 2 =
      Int.subNatNat (u * u) (5 * (b * b)) := by
  rw [int_sq_nat u, int_sq_nat b]
  change ((u * u : Nat) : Int) - (5 : Int) * ((b * b : Nat) : Int) =
    Int.subNatNat (u * u) (5 * (b * b))
  rw [show (5 : Int) * ((b * b : Nat) : Int) =
      ((5 * (b * b) : Nat) : Int) by
    change ((5 : Nat) : Int) * ((b * b : Nat) : Int) =
      ((5 * (b * b) : Nat) : Int)
    exact Int.ofNat_mul_ofNat 5 (b * b)]
  exact ofNat_sub_ofNat_eq_subNatNat (u * u) (5 * (b * b))

private theorem mul_four_succ (n : Nat) :
    4 * (n + 1) = 4 * n + 4 := by
  rw [Nat.mul_succ]

private theorem four_mul_zero :
    4 * 0 = 0 := by
  rfl

private theorem four_mul_subNatNat : ∀ (p q : Nat),
    (4 : Int) * Int.subNatNat p q = Int.subNatNat (4 * p) (4 * q)
  | 0, 0 => rfl
  | 0, _ + 1 => by
      rfl
  | p + 1, 0 => by
      rw [four_mul_zero]
      rw [subNatNat_zero_right p]
      change (4 : Int) * Int.ofNat (p + 1) = Int.subNatNat (4 * (p + 1)) 0
      rw [show (4 : Int) * Int.ofNat (p + 1) = Int.ofNat (4 * (p + 1)) by
        change Int.ofNat 4 * Int.ofNat (p + 1) = Int.ofNat (4 * (p + 1))
        exact Int.ofNat_mul_ofNat 4 (p + 1)]
      unfold Int.subNatNat
      rw [Nat.zero_sub]
      rw [Nat.sub_zero]
  | p + 1, q + 1 => by
      rw [subNatNat_succ_succ p q]
      change (4 : Int) * Int.subNatNat p q =
        Int.subNatNat (4 * (p + 1)) (4 * (q + 1))
      rw [mul_four_succ p, mul_four_succ q]
      rw [subNatNat_add_add_right (4 * p) (4 * q) 4]
      exact four_mul_subNatNat p q

private theorem rhs_to_sub (p q : Nat) :
    (4 : Int) * (((p : Nat) : Int) - ((q : Nat) : Int)) =
      Int.subNatNat (4 * p) (4 * q) := by
  rw [ofNat_sub_ofNat_eq_subNatNat p q]
  exact four_mul_subNatNat p q

private theorem norm_det_nat (a b : Nat) :
    (((b + a + a : Nat) : Int)) ^ 2 - 5 * (((b : Nat) : Int)) ^ 2 =
      4 * ((((b + a : Nat) : Int) * ((a : Nat) : Int)) -
        (((b : Nat) : Int) * ((b : Nat) : Int))) := by
  rw [lhs_to_sub (b + a + a) b]
  rw [show ((b + a : Nat) : Int) * ((a : Nat) : Int) =
      (((b + a) * a : Nat) : Int) by
    exact Int.ofNat_mul_ofNat (b + a) a]
  rw [show ((b : Nat) : Int) * ((b : Nat) : Int) =
      ((b * b : Nat) : Int) by
    exact Int.ofNat_mul_ofNat b b]
  rw [rhs_to_sub ((b + a) * a) (b * b)]
  exact subNatNat_cross_eq ((b + a + a) * (b + a + a)) (5 * (b * b))
    (4 * ((b + a) * a)) (4 * (b * b)) (norm_cross_nat a b)

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

/--
Universal proof of the Lucas-Fibonacci norm identity
`L_n^2 - 5 F_n^2 = 4*(-1)^n` for every natural index.
The proof rewrites `L_(k+1)` as `F_(k+2)+F_k`, identifies
`L_n^2 - 5F_n^2` with `4*det(M^n)` by first-principles integer algebra,
and then applies the checked Cassini determinant identity
`det(M^n)=altSign n`.  Thus the norm relation is exactly the Cassini
determinant relation scaled by four.
-/
theorem lucas_fib_norm_universal (n : Nat) :
    ((BEDC.Derived.Window6Lucas.lucas n : Int)) ^ 2
      - 5 * ((BEDC.Derived.Window6Fibonacci.fib n : Int)) ^ 2
      = 4 * BEDC.Derived.Window6Transfer.altSign n := by
  cases n with
  | zero =>
      rfl
  | succ k =>
      rw [BEDC.Derived.Window6Lucas.lucas_eq_fib_add k]
      rw [← BEDC.Derived.Window6Transfer.cassini (k + 1)]
      rw [BEDC.Derived.Window6Transfer.M_pow_fib]
      unfold BEDC.Derived.Window6Transfer.det
      rw [show ((BEDC.Derived.Window6Fibonacci.fib (k + 2) +
            BEDC.Derived.Window6Fibonacci.fib k : Nat) : Int) =
          ((BEDC.Derived.Window6Fibonacci.fib (k + 2) : Nat) : Int) +
            ((BEDC.Derived.Window6Fibonacci.fib k : Nat) : Int) by
        exact (Int.ofNat_add_ofNat
          (BEDC.Derived.Window6Fibonacci.fib (k + 2))
          (BEDC.Derived.Window6Fibonacci.fib k)).symm]
      have hrec : ((BEDC.Derived.Window6Fibonacci.fib (k + 2) : Nat) : Int) =
          ((BEDC.Derived.Window6Fibonacci.fib (k + 1) : Nat) : Int) +
            ((BEDC.Derived.Window6Fibonacci.fib k : Nat) : Int) := by
        change ((BEDC.Derived.Window6Fibonacci.fib (k + 1) +
            BEDC.Derived.Window6Fibonacci.fib k : Nat) : Int) =
          ((BEDC.Derived.Window6Fibonacci.fib (k + 1) : Nat) : Int) +
            ((BEDC.Derived.Window6Fibonacci.fib k : Nat) : Int)
        exact (Int.ofNat_add_ofNat
          (BEDC.Derived.Window6Fibonacci.fib (k + 1))
          (BEDC.Derived.Window6Fibonacci.fib k)).symm
      rw [hrec]
      exact norm_det_nat
        (BEDC.Derived.Window6Fibonacci.fib k)
        (BEDC.Derived.Window6Fibonacci.fib (k + 1))

example :
    ((BEDC.Derived.Window6Lucas.lucas 5 : Int)) ^ 2 -
        5 * ((BEDC.Derived.Window6Fibonacci.fib 5 : Int)) ^ 2 = -4 := by
  decide

example :
    ((BEDC.Derived.Window6Lucas.lucas 8 : Int)) ^ 2 -
        5 * ((BEDC.Derived.Window6Fibonacci.fib 8 : Int)) ^ 2 = 4 := by
  decide

end BEDC.Derived.Window6LucasFibNormRelation
