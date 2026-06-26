import BEDC.Derived.BernoulliPolyUp
import BEDC.Algebra.FiniteFold

namespace BEDC.Derived.FaulhaberUp

open BEDC.Derived.BernoulliUp
open BEDC.Derived.BernoulliPolyUp

def powNat (x : Nat) : Nat -> Nat
  | 0 => 1
  | Nat.succ p => x * powNat x p

def powerSumNat (p : Nat) : Nat -> Nat
  | 0 => 0
  | Nat.succ n => powerSumNat p n + powNat (Nat.succ n) p

def powerSumRange (p n : Nat) : List Nat :=
  match n with
  | 0 => []
  | Nat.succ m => powerSumRange p m ++ [powNat (Nat.succ m) p]

def sumNatList : List Nat -> Nat
  | [] => 0
  | x :: xs => x + sumNatList xs

private theorem sumNatList_append_singleton (xs : List Nat) (x : Nat) :
    sumNatList (xs ++ [x]) = sumNatList xs + x := by
  induction xs with
  | nil =>
      rw [List.nil_append]
      unfold sumNatList
      exact Nat.add_comm x 0
  | cons y ys ih =>
      change y + sumNatList (ys ++ [x]) = y + sumNatList ys + x
      rw [ih]
      exact (Nat.add_assoc y (sumNatList ys) x).symm

def rawOfNat (n : Nat) : RawRat :=
  { num := Int.ofNat n, denMinusOne := 0 }

def rawPowNat (x p : Nat) : RawRat :=
  rawOfNat (powNat x p)

def rawPowerSum (p : Nat) : Nat -> RawRat
  | 0 => rawZero
  | Nat.succ n => rawAdd (rawPowerSum p n) (rawPowNat (Nat.succ n) p)

def rawMul (x y : RawRat) : RawRat :=
  rawNormalize
    { num := x.num * y.num
      denMinusOne := x.den * y.den - 1 }

def rawDivNat (x : RawRat) (denMinusOne : Nat) : RawRat :=
  rawScaleDen x denMinusOne

def rawPowerSumOneClosed (n : Nat) : RawRat :=
  rawDivNat (rawMul (rawOfNat n) (rawOfNat (n + 1))) 1

def rawPowerSumTwoClosed (n : Nat) : RawRat :=
  rawDivNat
    (rawMul (rawMul (rawOfNat n) (rawOfNat (n + 1)))
      (rawOfNat (2 * n + 1))) 5

def rawPowerSumThreeClosed (n : Nat) : RawRat :=
  rawMul
    (rawDivNat (rawMul (rawOfNat n) (rawOfNat (n + 1))) 1)
    (rawDivNat (rawMul (rawOfNat n) (rawOfNat (n + 1))) 1)

def rawFaulhaberTerm (p j x : Nat) : RawRat :=
  rawMul
    (rawBernoulliPolyCoeffAt (p + 1) j)
    (rawOfNat (powNat x (p + 1 - j)))

def rawFaulhaberSumFrom (p fuel j x : Nat) : RawRat :=
  match fuel with
  | 0 => rawZero
  | Nat.succ fuel' =>
      rawAdd (rawFaulhaberTerm p j x)
        (rawFaulhaberSumFrom p fuel' (Nat.succ j) x)

def rawFaulhaberBernoulliPolyEval (p x : Nat) : RawRat :=
  rawFaulhaberSumFrom p (p + 2) 0 x

def rawFaulhaberFormula (p n : Nat) : RawRat :=
  rawDivNat
    (rawAdd
      (rawFaulhaberBernoulliPolyEval p (n + 1))
      (rawNeg (rawFaulhaberBernoulliPolyEval p 1)))
    p

def faulhaberFormula (p n : Nat) : RationalUp.RatNum :=
  rawRatToRat (rawFaulhaberFormula p n)

def powerSumUp (p n : FKernel.Hist.BHist) : RationalUp.RatNum :=
  rawRatToRat
    (rawPowerSum
      (FKernel.ExternalBinary.bwordLength p)
      (FKernel.ExternalBinary.bwordLength n))

theorem powNat_zero (x : Nat) :
    powNat x 0 = 1 := by
  rfl

theorem powNat_one (x : Nat) :
    powNat x 1 = x := by
  unfold powNat
  exact Nat.mul_one x

theorem powNat_two (x : Nat) :
    powNat x 2 = x * x := by
  unfold powNat
  rw [powNat_one]

private theorem natMulAssocPure (a b c : Nat) :
    (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      calc
        (a * b) * Nat.succ c = (a * b) * c + a * b := Nat.mul_succ (a * b) c
        _ = a * (b * c) + a * b := congrArg (fun x => x + a * b) ih
        _ = a * (b * c + b) := (Nat.mul_add a (b * c) b).symm
        _ = a * (b * Nat.succ c) := congrArg (fun x => a * x) (Nat.mul_succ b c).symm

private theorem natRightDistribPure (a b c : Nat) :
    (a + b) * c = a * c + b * c := by
  calc
    (a + b) * c = c * (a + b) := Nat.mul_comm (a + b) c
    _ = c * a + c * b := Nat.left_distrib c a b
    _ = a * c + c * b := congrArg (fun x => x + c * b) (Nat.mul_comm c a)
    _ = a * c + b * c := congrArg (fun x => a * c + x) (Nat.mul_comm c b)

private theorem natMulLeftCommPure (a b c : Nat) :
    a * (b * c) = b * (a * c) := by
  calc
    a * (b * c) = (a * b) * c := (natMulAssocPure a b c).symm
    _ = (b * a) * c := congrArg (fun x => x * c) (Nat.mul_comm a b)
    _ = b * (a * c) := natMulAssocPure b a c

private theorem natAddFourSwap (a b c d : Nat) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  calc
    (a + b) + (c + d) = a + (b + (c + d)) := Nat.add_assoc a b (c + d)
    _ = a + ((b + c) + d) :=
      congrArg (fun t => a + t) (Nat.add_assoc b c d).symm
    _ = a + ((c + b) + d) :=
      congrArg (fun t => a + (t + d)) (Nat.add_comm b c)
    _ = a + (c + (b + d)) :=
      congrArg (fun t => a + t) (Nat.add_assoc c b d)
    _ = (a + c) + (b + d) := (Nat.add_assoc a c (b + d)).symm

private def polyEval : List Nat -> Nat -> Nat
  | [], _ => 0
  | c :: cs, x => c + x * polyEval cs x

private def polyAdd : List Nat -> List Nat -> List Nat
  | [], q => q
  | p, [] => p
  | c :: cs, d :: ds => (c + d) :: polyAdd cs ds

private def polyScale (k : Nat) : List Nat -> List Nat
  | [] => []
  | c :: cs => (k * c) :: polyScale k cs

private def polyMul (p q : List Nat) : List Nat :=
  match p with
  | [] => []
  | c :: cs => polyAdd (polyScale c q) (0 :: polyMul cs q)

private theorem polyEval_add_context (c d x a b : Nat) :
    c + d + x * (a + b) = (c + x * a) + (d + x * b) := by
  rw [Nat.left_distrib]
  exact natAddFourSwap c d (x * a) (x * b)

private theorem polyEval_add (p q : List Nat) (x : Nat) :
    polyEval (polyAdd p q) x = polyEval p x + polyEval q x := by
  induction p generalizing q with
  | nil =>
      cases q with
      | nil =>
          rfl
      | cons d ds =>
          exact (Nat.zero_add (d + x * polyEval ds x)).symm
  | cons c cs ih =>
      cases q with
      | nil =>
          exact (Nat.add_zero (c + x * polyEval cs x)).symm
      | cons d ds =>
          change c + d + x * polyEval (polyAdd cs ds) x =
            (c + x * polyEval cs x) + (d + x * polyEval ds x)
          rw [ih ds]
          exact polyEval_add_context c d x (polyEval cs x) (polyEval ds x)

private theorem polyEval_scale (k : Nat) (p : List Nat) (x : Nat) :
    polyEval (polyScale k p) x = k * polyEval p x := by
  induction p with
  | nil =>
      exact (Nat.mul_zero k).symm
  | cons c cs ih =>
      change k * c + x * polyEval (polyScale k cs) x =
        k * (c + x * polyEval cs x)
      rw [ih]
      rw [Nat.left_distrib]
      exact congrArg (fun t => k * c + t)
        (natMulLeftCommPure x k (polyEval cs x))

private theorem polyEval_shift (p : List Nat) (x : Nat) :
    polyEval (0 :: p) x = x * polyEval p x := by
  change 0 + x * polyEval p x = x * polyEval p x
  exact Nat.zero_add (x * polyEval p x)

private theorem polyEval_mul (p q : List Nat) (x : Nat) :
    polyEval (polyMul p q) x = polyEval p x * polyEval q x := by
  induction p with
  | nil =>
      exact (Nat.zero_mul (polyEval q x)).symm
  | cons c cs ih =>
      change polyEval (polyAdd (polyScale c q) (0 :: polyMul cs q)) x =
        (c + x * polyEval cs x) * polyEval q x
      rw [polyEval_add]
      rw [polyEval_scale]
      rw [polyEval_shift]
      rw [ih]
      calc
        c * polyEval q x + x * (polyEval cs x * polyEval q x) =
            c * polyEval q x + (x * polyEval cs x) * polyEval q x :=
          congrArg (fun t => c * polyEval q x + t)
            (natMulAssocPure x (polyEval cs x) (polyEval q x)).symm
        _ = (c + x * polyEval cs x) * polyEval q x :=
          (natRightDistribPure c (x * polyEval cs x) (polyEval q x)).symm

private inductive PExpr where
  | var : PExpr
  | const : Nat -> PExpr
  | add : PExpr -> PExpr -> PExpr
  | mul : PExpr -> PExpr -> PExpr

private def PExpr.eval : PExpr -> Nat -> Nat
  | .var, x => x
  | .const c, _ => c
  | .add a b, x => PExpr.eval a x + PExpr.eval b x
  | .mul a b, x => PExpr.eval a x * PExpr.eval b x

private def PExpr.norm : PExpr -> List Nat
  | .var => [0, 1]
  | .const c => [c]
  | .add a b => polyAdd (PExpr.norm a) (PExpr.norm b)
  | .mul a b => polyMul (PExpr.norm a) (PExpr.norm b)

private theorem PExpr.norm_sound (e : PExpr) (x : Nat) :
    PExpr.eval e x = polyEval (PExpr.norm e) x := by
  induction e with
  | var =>
      change x = 0 + x * (1 + x * 0)
      rw [Nat.mul_zero]
      rw [Nat.add_zero]
      rw [Nat.mul_one]
      exact (Nat.zero_add x).symm
  | const c =>
      change c = c + x * 0
      rw [Nat.mul_zero]
      exact (Nat.add_zero c).symm
  | add a b iha ihb =>
      change PExpr.eval a x + PExpr.eval b x =
        polyEval (polyAdd (PExpr.norm a) (PExpr.norm b)) x
      rw [iha, ihb]
      exact (polyEval_add (PExpr.norm a) (PExpr.norm b) x).symm
  | mul a b iha ihb =>
      change PExpr.eval a x * PExpr.eval b x =
        polyEval (polyMul (PExpr.norm a) (PExpr.norm b)) x
      rw [iha, ihb]
      exact (polyEval_mul (PExpr.norm a) (PExpr.norm b) x).symm

private theorem PExpr.eq_of_norm_eq (left right : PExpr)
    (same : left.norm = right.norm) (x : Nat) :
    left.eval x = right.eval x := by
  calc
    left.eval x = polyEval left.norm x := PExpr.norm_sound left x
    _ = polyEval right.norm x := congrArg (fun p => polyEval p x) same
    _ = right.eval x := (PExpr.norm_sound right x).symm

private def X : PExpr := .var

private def C (n : Nat) : PExpr := .const n

private def A (x y : PExpr) : PExpr := .add x y

private def M (x y : PExpr) : PExpr := .mul x y

private def oneStepLeft : PExpr :=
  A (M X (A X (C 1))) (M (C 2) (A X (C 1)))

private def oneStepRight : PExpr :=
  M (A X (C 1)) (A X (C 2))

private def twoStepLeft : PExpr :=
  A (M (M X (A X (C 1))) (A (M (C 2) X) (C 1)))
    (M (C 6) (M (A X (C 1)) (A X (C 1))))

private def twoStepRight : PExpr :=
  M (M (A X (C 1)) (A X (C 2)))
    (A (M (C 2) (A X (C 1))) (C 1))

private def threeStepLeft : PExpr :=
  A (M (M (M X X) (A X (C 1))) (A X (C 1)))
    (M (C 4) (M (M (A X (C 1)) (A X (C 1))) (A X (C 1))))

private def threeStepRight : PExpr :=
  M (M (M (A X (C 1)) (A X (C 1))) (A X (C 2))) (A X (C 2))

theorem powNat_three (x : Nat) :
    powNat x 3 = x * x * x := by
  unfold powNat
  rw [powNat_two]
  exact (natMulAssocPure x x x).symm

theorem powerSumNat_zero (p : Nat) :
    powerSumNat p 0 = 0 := by
  rfl

theorem powerSumNat_succ (p n : Nat) :
    powerSumNat p (Nat.succ n) =
      powerSumNat p n + powNat (Nat.succ n) p := by
  rfl

theorem powerSumRange_sum (p n : Nat) :
    sumNatList (powerSumRange p n) = powerSumNat p n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      unfold powerSumRange
      rw [sumNatList_append_singleton]
      rw [ih]
      rfl

theorem rawPowerSum_zero (p : Nat) :
    rawPowerSum p 0 = rawZero := by
  rfl

theorem rawPowerSum_succ (p n : Nat) :
    rawPowerSum p (Nat.succ n) =
      rawAdd (rawPowerSum p n) (rawPowNat (Nat.succ n) p) := by
  rfl

theorem rawFaulhaberFormula_def (p n : Nat) :
    rawFaulhaberFormula p n =
      rawDivNat
        (rawAdd
          (rawFaulhaberBernoulliPolyEval p (n + 1))
          (rawNeg (rawFaulhaberBernoulliPolyEval p 1)))
        p := by
  rfl

theorem rawFaulhaberSumFrom_zero (p j n : Nat) :
    rawFaulhaberSumFrom p 0 j n = rawZero := by
  rfl

theorem rawFaulhaberSumFrom_succ (p fuel j n : Nat) :
    rawFaulhaberSumFrom p (Nat.succ fuel) j n =
      rawAdd (rawFaulhaberTerm p j n)
        (rawFaulhaberSumFrom p fuel (Nat.succ j) n) := by
  rfl

private theorem one_closed_step (n : Nat) :
    n * (n + 1) + 2 * (n + 1) = (n + 1) * (n + 2) := by
  change oneStepLeft.eval n = oneStepRight.eval n
  exact PExpr.eq_of_norm_eq oneStepLeft oneStepRight rfl n

private theorem two_closed_step (n : Nat) :
    n * (n + 1) * (2 * n + 1) + 6 * ((n + 1) * (n + 1)) =
      (n + 1) * (n + 2) * (2 * (n + 1) + 1) := by
  change twoStepLeft.eval n = twoStepRight.eval n
  exact PExpr.eq_of_norm_eq twoStepLeft twoStepRight rfl n

private theorem three_closed_step (n : Nat) :
    n * n * (n + 1) * (n + 1) + 4 * ((n + 1) * (n + 1) * (n + 1)) =
      (n + 1) * (n + 1) * (n + 2) * (n + 2) := by
  change threeStepLeft.eval n = threeStepRight.eval n
  exact PExpr.eq_of_norm_eq threeStepLeft threeStepRight rfl n

theorem powerSum_one_closed_scaled (n : Nat) :
    2 * powerSumNat 1 n = n * (n + 1) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      unfold powerSumNat
      rw [powNat_one]
      rw [Nat.left_distrib]
      rw [ih]
      exact one_closed_step n

theorem rawPowerSum_one_closed (n : Nat) :
    2 * powerSumNat 1 n = n * (n + 1) :=
  powerSum_one_closed_scaled n

theorem powerSum_two_closed_scaled (n : Nat) :
    6 * powerSumNat 2 n = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change 6 * (powerSumNat 2 n + powNat (n + 1) 2) =
        (n + 1) * (n + 2) * (2 * (n + 1) + 1)
      rw [Nat.left_distrib]
      rw [ih]
      rw [powNat_two]
      exact two_closed_step n

theorem rawPowerSum_two_closed (n : Nat) :
    6 * powerSumNat 2 n = n * (n + 1) * (2 * n + 1) :=
  powerSum_two_closed_scaled n

theorem powerSum_three_closed_scaled (n : Nat) :
    4 * powerSumNat 3 n = n * n * (n + 1) * (n + 1) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change 4 * (powerSumNat 3 n + powNat (n + 1) 3) =
        (n + 1) * (n + 1) * (n + 2) * (n + 2)
      rw [Nat.left_distrib]
      rw [ih]
      rw [powNat_three]
      exact three_closed_step n

theorem rawPowerSum_three_closed (n : Nat) :
    4 * powerSumNat 3 n = n * n * (n + 1) * (n + 1) :=
  powerSum_three_closed_scaled n

theorem rawFaulhaber_formula (p n : Nat) :
    rawFaulhaberFormula p n =
      rawDivNat
        (rawAdd
          (rawFaulhaberBernoulliPolyEval p (n + 1))
          (rawNeg (rawFaulhaberBernoulliPolyEval p 1)))
        p := by
  rfl

theorem rawFaulhaber_small_zero :
    rawFaulhaberFormula 0 5 = rawPowerSum 0 5 := by
  rfl

theorem rawFaulhaber_small_one :
    rawFaulhaberFormula 1 3 = rawPowerSum 1 3 := by
  rfl

theorem rawFaulhaber_small_two :
    rawFaulhaberFormula 2 3 = rawPowerSum 2 3 := by
  rfl

theorem rawFaulhaber_small_three :
    rawFaulhaberFormula 3 3 = rawPowerSum 3 3 := by
  rfl

theorem powerSumNat_small_values :
    powerSumNat 1 3 = 6 ∧
      powerSumNat 2 3 = 14 ∧
      powerSumNat 3 3 = 36 := by
  exact ⟨rfl, rfl, rfl⟩

end BEDC.Derived.FaulhaberUp
