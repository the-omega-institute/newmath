/-
Fibonacci--Polya Jensen kernel lambda-deformation.

The family W_m(lambda D) interpolates between the actual reciprocal Jensen
polynomial of the Riemann xi function at lambda = 0 and the Fibonacci-cube
smoothed window at lambda = 1.  In degree two its symbolic discriminant is

  disc F^{(lambda)}_{m,2,n}
    = 4 * ((gamma_{n+1}^2 - gamma_n * gamma_{n+2})
        + (3*m - 2) * lambda^2 * gamma_n^2).

The certificate is a finite algebraic normal-form calculation with symbolic xi
coefficients.  It is not an RH proof and not a Zeckendorf model of xi
coefficients.
-/

namespace BEDC.Derived.FibonacciPolyaJensenDeformation

inductive Var5 where
  | m
  | a
  | b
  | c
  | L
deriving BEq

structure Mon5 where
  m : Nat
  a : Nat
  b : Nat
  c : Nat
  L : Nat
deriving BEq

structure Term5 where
  coeff : Int
  mon : Mon5
deriving BEq

abbrev Poly5 := List Term5

def monRank (x : Mon5) : Nat :=
  x.m * 100000000 + x.a * 1000000 + x.b * 10000 + x.c * 100 + x.L

def monLe (x y : Mon5) : Bool :=
  monRank x <= monRank y

def insertTerm (t : Term5) : Poly5 -> Poly5
| [] => if t.coeff == 0 then [] else [t]
| u :: us =>
    if t.coeff == 0 then
      u :: us
    else if t.mon == u.mon then
      let s := t.coeff + u.coeff
      if s == 0 then us else { coeff := s, mon := u.mon } :: us
    else if monLe t.mon u.mon then
      t :: u :: us
    else
      u :: insertTerm t us

def norm : Poly5 -> Poly5
| [] => []
| t :: ts => insertTerm t (norm ts)

def padd (p q : Poly5) : Poly5 :=
  norm (p ++ q)

def pneg (p : Poly5) : Poly5 :=
  p.map (fun t => { coeff := -t.coeff, mon := t.mon })

def psub (p q : Poly5) : Poly5 :=
  padd p (pneg q)

def mmul (x y : Mon5) : Mon5 :=
  { m := x.m + y.m, a := x.a + y.a, b := x.b + y.b, c := x.c + y.c, L := x.L + y.L }

def tmul (x y : Term5) : Term5 :=
  { coeff := x.coeff * y.coeff, mon := mmul x.mon y.mon }

def pmulRaw : Poly5 -> Poly5 -> Poly5
| [], _ => []
| x :: xs, q => (q.map (fun y => tmul x y)) ++ pmulRaw xs q

def pmul (p q : Poly5) : Poly5 :=
  norm (pmulRaw p q)

def pconst (z : Int) : Poly5 :=
  if z == 0 then [] else [{ coeff := z, mon := { m := 0, a := 0, b := 0, c := 0, L := 0 } }]

def pvar : Var5 -> Poly5
| .m => [{ coeff := 1, mon := { m := 1, a := 0, b := 0, c := 0, L := 0 } }]
| .a => [{ coeff := 1, mon := { m := 0, a := 1, b := 0, c := 0, L := 0 } }]
| .b => [{ coeff := 1, mon := { m := 0, a := 0, b := 1, c := 0, L := 0 } }]
| .c => [{ coeff := 1, mon := { m := 0, a := 0, b := 0, c := 1, L := 0 } }]
| .L => [{ coeff := 1, mon := { m := 0, a := 0, b := 0, c := 0, L := 1 } }]

instance : OfNat Poly5 n where
  ofNat := pconst (Int.ofNat n)

instance : Add Poly5 where
  add := padd

instance : Neg Poly5 where
  neg := pneg

instance : Sub Poly5 where
  sub := psub

instance : Mul Poly5 where
  mul := pmul

def M : Poly5 :=
  pvar .m

def A : Poly5 :=
  pvar .a

def B : Poly5 :=
  pvar .b

def C : Poly5 :=
  pvar .c

def L : Poly5 :=
  pvar .L

def discFlamPoly : Poly5 :=
  (2 * A * M * L + 2 * B) * (2 * A * M * L + 2 * B) -
    4 * A * (A * L * L * M * M - 3 * A * L * L * M + 2 * A * L * L + 2 * B * M * L + C)

def turanDiscPoly : Poly5 :=
  4 * (B * B - A * C)

def fibKernelLamPoly : Poly5 :=
  4 * (3 * M - 2) * L * L * A * A

theorem fib_jensen_lambda_disc_identity :
    (discFlamPoly == turanDiscPoly + fibKernelLamPoly) = true := by
  rfl

def discFlamAtL0Poly : Poly5 :=
  (2 * B) * (2 * B) - 4 * A * C

theorem fib_jensen_lambda_zero_disc_identity :
    (discFlamAtL0Poly == turanDiscPoly) = true := by
  rfl

def discFlamAtL1Poly : Poly5 :=
  (2 * A * M + 2 * B) * (2 * A * M + 2 * B) -
    4 * A * (A * M * M - 3 * A * M + 2 * A + 2 * B * M + C)

def fibKernelAtL1Poly : Poly5 :=
  4 * (3 * M - 2) * A * A

theorem fib_jensen_lambda_one_disc_identity :
    (discFlamAtL1Poly == turanDiscPoly + fibKernelAtL1Poly) = true := by
  rfl

theorem fib_lambda_margin :
    (discFlamPoly - turanDiscPoly == fibKernelLamPoly) = true := by
  rfl

def fibKernelLamNat (m a L : Nat) : Nat :=
  4 * (3 * m + 1) * L * L * a * a

theorem fibKernelLamNat_nonnegative (m a L : Nat) :
    (0 : Int) <= Int.ofNat (fibKernelLamNat m a L) := by
  change (Int.ofNat (fibKernelLamNat m a L) - Int.ofNat 0).NonNeg
  unfold HSub.hSub Int.instSub Int.sub
  change (Int.ofNat (fibKernelLamNat m a L) + -Int.ofNat 0).NonNeg
  change (Int.ofNat (fibKernelLamNat m a L) + Int.ofNat 0).NonNeg
  unfold HAdd.hAdd instHAdd Add.add Int.instAdd Int.add
  exact Int.NonNeg.mk (fibKernelLamNat m a L)

theorem fibonacci_polya_jensen_deformation_certificate :
    (discFlamPoly == turanDiscPoly + fibKernelLamPoly) = true ∧
    (discFlamAtL0Poly == turanDiscPoly) = true ∧
    (discFlamAtL1Poly == turanDiscPoly + fibKernelAtL1Poly) = true ∧
    (discFlamPoly - turanDiscPoly == fibKernelLamPoly) = true ∧
    (forall m a L : Nat, (0 : Int) <= Int.ofNat (fibKernelLamNat m a L)) := by
  constructor
  · exact fib_jensen_lambda_disc_identity
  constructor
  · exact fib_jensen_lambda_zero_disc_identity
  constructor
  · exact fib_jensen_lambda_one_disc_identity
  constructor
  · exact fib_lambda_margin
  · exact fibKernelLamNat_nonnegative

end BEDC.Derived.FibonacciPolyaJensenDeformation
