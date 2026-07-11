import BEDC.Derived.FibonacciUp
import BEDC.Derived.ZeckendorfUp
import BEDC.Derived.Window6GoldenPentagonRPLink

namespace BEDC.Derived.RHRoute.SelfSimilarTwoFace

/-!
Algebraic kernel for the self-similar two-face packet.

The carrier is the existing BEDC golden ring `Zphi`, written as pairs
`a + b phi` with `phi^2 = phi + 1`.  This file records only exact
integer algebra.  Window bounds, density statements, model-set analysis,
and RH dictionary claims are represented below as obligation surfaces,
not as inhabitants.
-/

abbrev ZPhi : Type :=
  BEDC.Derived.Window6GoldenPentagonRPLink.Zphi

def zmk (a b : Int) : ZPhi :=
  BEDC.Derived.Window6GoldenPentagonRPLink.Zphi.mk a b

def zzero : ZPhi :=
  BEDC.Derived.Window6GoldenPentagonRPLink.zzero

def zone : ZPhi :=
  BEDC.Derived.Window6GoldenPentagonRPLink.zone

def phi : ZPhi :=
  BEDC.Derived.Window6GoldenPentagonRPLink.phi

def sqrt5 : ZPhi :=
  BEDC.Derived.Window6GoldenPentagonRPLink.sqrt5

def zadd (x y : ZPhi) : ZPhi :=
  BEDC.Derived.Window6GoldenPentagonRPLink.zadd x y

def zsub (x y : ZPhi) : ZPhi :=
  BEDC.Derived.Window6GoldenPentagonRPLink.zsub x y

def zmul (x y : ZPhi) : ZPhi :=
  BEDC.Derived.Window6GoldenPentagonRPLink.zmul x y

def zneg (x : ZPhi) : ZPhi :=
  zmk (-x.a) (-x.b)

def zint (n : Int) : ZPhi :=
  zmk n 0

def zscale (n : Int) (x : ZPhi) : ZPhi :=
  zmul (zint n) x

private theorem int_nat_mul_zero (n : Nat) :
    Int.ofNat n * (0 : Int) = 0 := by
  change Int.ofNat (n * 0) = Int.ofNat 0
  exact congrArg Int.ofNat (Nat.mul_zero n)

private theorem int_nat_mul_one (n : Nat) :
    Int.ofNat n * (1 : Int) = Int.ofNat n := by
  change Int.ofNat (n * 1) = Int.ofNat n
  exact congrArg Int.ofNat (Nat.mul_one n)

private theorem int_nat_zero_add (n : Nat) :
    (0 : Int) + Int.ofNat n = Int.ofNat n := by
  change Int.ofNat (0 + n) = Int.ofNat n
  exact congrArg Int.ofNat (Nat.zero_add n)

private theorem int_nat_add_zero (n : Nat) :
    Int.ofNat n + (0 : Int) = Int.ofNat n := by
  change Int.ofNat (n + 0) = Int.ofNat n
  exact congrArg Int.ofNat (Nat.add_zero n)

private theorem int_nat_add (m n : Nat) :
    Int.ofNat m + Int.ofNat n = Int.ofNat (m + n) := by
  exact (Int.ofNat_add_ofNat m n).symm

private theorem zphi_eq {x y : ZPhi}
    (ha : x.a = y.a) (hb : x.b = y.b) : x = y := by
  cases x with
  | mk xa xb =>
      cases y with
      | mk ya yb =>
          cases ha
          cases hb
          rfl

/-- Galois conjugation on `Z[phi]`: `phi` is sent to `psi = 1 - phi`. -/
def conj (x : ZPhi) : ZPhi :=
  zmk (x.a + x.b) (-x.b)

def psi : ZPhi :=
  conj phi

/-- The integral trace of `a + b phi` is `(a + b phi) + (a + b psi) = 2a + b`. -/
def trace (x : ZPhi) : Int :=
  x.a + (conj x).a

theorem phi_square :
    zmul phi phi = zadd phi zone :=
  BEDC.Derived.Window6GoldenPentagonRPLink.phi_sq

theorem sqrt5_square :
    zmul sqrt5 sqrt5 = zmk 5 0 :=
  BEDC.Derived.Window6GoldenPentagonRPLink.sqrt5_sq

theorem sqrt5_coords :
    sqrt5 = zmk (-1) 2 :=
  BEDC.Derived.Window6GoldenPentagonRPLink.concrete_sqrt5_coords

theorem psi_coords :
    psi = zmk 1 (-1) := by
  rfl

theorem conj_phi :
    conj phi = psi := by
  rfl

theorem trace_integer_carrier (x : ZPhi) :
    exists n : Int, trace x = n := by
  exact Exists.intro (trace x) rfl

theorem galois_fixed_integer_axis (x : ZPhi) :
    conj x = x -> exists n : Int, x = zint n := by
  cases x with
  | mk a b =>
      intro h
      change zmk (a + b) (-b) = zmk a b at h
      injection h with _ hb
      cases b with
      | ofNat n =>
          cases n with
          | zero =>
              exact Exists.intro a rfl
          | succ n =>
              cases hb
      | negSucc n =>
          cases hb

def zpow (x : ZPhi) : Nat -> ZPhi
  | 0 => zone
  | n + 1 => zmul (zpow x n) x

def phiPow (n : Nat) : ZPhi :=
  zpow phi n

def psiPow (n : Nat) : ZPhi :=
  zpow psi n

theorem phiPow_zero :
    phiPow 0 = zone := by
  rfl

theorem psiPow_zero :
    psiPow 0 = zone := by
  rfl

theorem phiPow_succ (n : Nat) :
    phiPow (n + 1) = zmul (phiPow n) phi := by
  rfl

theorem psiPow_succ (n : Nat) :
    psiPow (n + 1) = zmul (psiPow n) psi := by
  rfl

theorem phiPow_one :
    phiPow 1 = phi := by
  rfl

theorem psiPow_one :
    psiPow 1 = psi := by
  rfl

theorem phiPow_two :
    phiPow 2 = zadd phi zone := by
  rfl

theorem psiPow_two :
    psiPow 2 = zmk 2 (-1) := by
  rfl

abbrev fib : Nat -> Nat :=
  BEDC.Derived.FibonacciUp.fib

theorem phiPow_pair (n : Nat) :
    phiPow (n + 1) = zmk (Int.ofNat (fib n)) (Int.ofNat (fib (n + 1))) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [phiPow_succ, ih]
      apply zphi_eq
      · change Int.ofNat (fib n) * (0 : Int) + Int.ofNat (fib (n + 1)) * (1 : Int) =
          Int.ofNat (fib (n + 1))
        rw [int_nat_mul_zero, int_nat_mul_one, int_nat_zero_add]
      · change Int.ofNat (fib n) * (1 : Int) + Int.ofNat (fib (n + 1)) * (0 : Int) +
            Int.ofNat (fib (n + 1)) * (1 : Int) = Int.ofNat (fib (n + 1 + 1))
        rw [int_nat_mul_one, int_nat_mul_zero, int_nat_add_zero, int_nat_mul_one]
        rw [int_nat_add]
        exact congrArg Int.ofNat (Nat.add_comm (fib n) (fib (n + 1)))

/-- Numerator form of the Fibonacci Binet identity inside `Z[phi]`. -/
def binetNumerator (k : Nat) : ZPhi :=
  zsub (phiPow (k + 1)) (psiPow (k + 1))

def binetSqrt5Scale (k : Nat) : ZPhi :=
  zscale (Int.ofNat (fib (k + 1))) sqrt5

theorem binetNumerator_zero :
    binetNumerator 0 = binetSqrt5Scale 0 := by
  rfl

theorem binetNumerator_one :
    binetNumerator 1 = binetSqrt5Scale 1 := by
  rfl

theorem binetNumerator_two :
    binetNumerator 2 = binetSqrt5Scale 2 := by
  rfl

theorem binetNumerator_three :
    binetNumerator 3 = binetSqrt5Scale 3 := by
  rfl

theorem binetNumerator_four :
    binetNumerator 4 = binetSqrt5Scale 4 := by
  rfl

abbrev zeckendorf : Nat -> List Nat :=
  BEDC.Derived.ZeckendorfUp.zeckendorf

abbrev zeckendorfValue : List Nat -> Nat :=
  BEDC.Derived.ZeckendorfUp.zeckendorfValue

/-- The contraction-face readout `beta'` from Zeckendorf indices. -/
def betaPrimeDigits : List Nat -> ZPhi
  | [] => zzero
  | k :: ks => zadd (psiPow (k + 1)) (betaPrimeDigits ks)

def betaPrime (v : Nat) : ZPhi :=
  betaPrimeDigits (zeckendorf v)

/-- Pure `Z[phi]` deficit face: no logs, no real analysis. -/
def deficitFace (v₁ v₂ : Nat) : ZPhi :=
  zsub (zadd (betaPrime v₁) (betaPrime v₂)) (betaPrime (v₁ + v₂))

/-- The trace-carrier integer attached to the deficit face. -/
def deficitTrace (v₁ v₂ : Nat) : Int :=
  trace (deficitFace v₁ v₂)

theorem betaPrimeDigits_nil :
    betaPrimeDigits [] = zzero := by
  rfl

theorem betaPrimeDigits_cons (k : Nat) (ks : List Nat) :
    betaPrimeDigits (k :: ks) = zadd (psiPow (k + 1)) (betaPrimeDigits ks) := by
  rfl

theorem zeckendorf_readback (v : Nat) :
    zeckendorfValue (zeckendorf v) = v :=
  BEDC.Derived.ZeckendorfUp.zeckendorf_sum_restore v

theorem deficitTrace_has_integer_carrier (v₁ v₂ : Nat) :
    exists c : Int, deficitTrace v₁ v₂ = c := by
  exact Exists.intro (deficitTrace v₁ v₂) rfl

/-- The algebraic balance needed by the Galois proof of deficit integrality. -/
structure DeficitGaloisBalanceCertificate (v₁ v₂ : Nat) where
  balanced : conj (deficitFace v₁ v₂) = deficitFace v₁ v₂

theorem deficitFace_integer_axis_of_galois_balance {v₁ v₂ : Nat}
    (cert : DeficitGaloisBalanceCertificate v₁ v₂) :
    exists c : Int, deficitFace v₁ v₂ = zint c := by
  exact galois_fixed_integer_axis (deficitFace v₁ v₂) cert.balanced

/-- Window bounds are an obligation surface in this algebra-only module. -/
structure DeficitWindowBoundObligation (v : Nat) where
  lowerBound : ZPhi
  upperBound : ZPhi
  readout : ZPhi
  readout_eq_betaPrime : readout = betaPrime v
  lowerWitness : Type
  upperWitness : Type

/--
The three-value deficit theorem needs the external window inclusion for
all three beta-prime terms.  This structure names that missing surface
without manufacturing an inhabitant.
-/
structure DeficitThreeValueWindowObligation (v₁ v₂ : Nat) where
  left : DeficitWindowBoundObligation v₁
  right : DeficitWindowBoundObligation v₂
  sum : DeficitWindowBoundObligation (v₁ + v₂)

structure LinForm where
  x : Int
  y : Int

structure QuadCoeff where
  xx : Int
  xy : Int
  yy : Int

def qneg (q : QuadCoeff) : QuadCoeff :=
  { xx := -q.xx, xy := -q.xy, yy := -q.yy }

def qadd (q r : QuadCoeff) : QuadCoeff :=
  { xx := q.xx + r.xx, xy := q.xy + r.xy, yy := q.yy + r.yy }

def qsub (q r : QuadCoeff) : QuadCoeff :=
  qadd q (qneg r)

def linSquare (l : LinForm) : QuadCoeff :=
  { xx := l.x * l.x, xy := l.x * l.y + l.y * l.x, yy := l.y * l.y }

def linMul (l m : LinForm) : QuadCoeff :=
  { xx := l.x * m.x
    xy := l.x * m.y + l.y * m.x
    yy := l.y * m.y }

def qOfPair (next cur : LinForm) : QuadCoeff :=
  qsub (qsub (linSquare next) (linMul next cur)) (linSquare cur)

/-- Coefficients of `Q(a,b)=a^2-ab-b^2`. -/
def frickeCoeff : QuadCoeff :=
  { xx := 1, xy := -1, yy := -1 }

/-- Fibonacci trace step on a pair `(u_{K+1}, u_K)`: `(a,b) -> (a+b,a)`. -/
def fibNextForm : LinForm :=
  { x := 1, y := 1 }

def fibCurForm : LinForm :=
  { x := 1, y := 0 }

theorem frickeCoeff_fibStep_antiInvariant :
    qOfPair fibNextForm fibCurForm = qneg frickeCoeff := by
  rfl

def evalQuad (q : QuadCoeff) (a b : Int) : Int :=
  q.xx * a * a + q.xy * a * b + q.yy * b * b

def frickeQ (a b : Int) : Int :=
  evalQuad frickeCoeff a b

theorem frickeQ_def (a b : Int) :
    frickeQ a b = (1 : Int) * a * a + (-1 : Int) * a * b + (-1 : Int) * b * b := by
  rfl

/-- Signed Cassini-Fricke ledger: the sign flips at each Fibonacci step. -/
def alternatingLedger (base : Int) : Nat -> Int
  | 0 => base
  | k + 1 => -alternatingLedger base k

def cassiniFrickeBase (A B : Int) : Int :=
  5 * A * B

def cassiniFrickeLedger (A B : Int) (K : Nat) : Int :=
  alternatingLedger (cassiniFrickeBase A B) K

theorem alternatingLedger_step (base : Int) (K : Nat) :
    alternatingLedger base (K + 1) = -alternatingLedger base K := by
  rfl

theorem cassiniFrickeLedger_antiInvariant (A B : Int) (K : Nat) :
    cassiniFrickeLedger A B (K + 1) = -cassiniFrickeLedger A B K := by
  rfl

structure AxisTraceState where
  W1 : ZPhi
  W0 : ZPhi
  t1 : ZPhi
  t0 : ZPhi

/-- Polynomial trace-map skeleton for `W_{K+1}=W_K+t_{K+1}W_{K-1}`. -/
def axisTraceStep (s : AxisTraceState) : AxisTraceState :=
  { W1 := zadd s.W1 (zmul (zmul s.t1 s.t0) s.W0)
    W0 := s.W1
    t1 := zmul s.t1 s.t0
    t0 := s.t1 }

theorem axisTraceStep_W_recurrence (s : AxisTraceState) :
    (axisTraceStep s).W1 = zadd s.W1 (zmul (zmul s.t1 s.t0) s.W0) := by
  rfl

theorem axisTraceStep_t_recurrence (s : AxisTraceState) :
    (axisTraceStep s).t1 = zmul s.t1 s.t0 := by
  rfl

/--
The RH dictionary bridge is an analytic obligation.  It is kept as a
carrier surface so the algebraic two-face kernel does not claim a zero
transport theorem.
-/
structure PullbackLineRHBridgeObligation where
  zetaVariable : ZPhi
  quasicrystalVariable : ZPhi
  divisorTransport : Type
  cancellationControl : Type

end BEDC.Derived.RHRoute.SelfSimilarTwoFace
