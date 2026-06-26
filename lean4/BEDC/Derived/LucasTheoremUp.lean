import BEDC.Derived.FactorialUp
import BEDC.Derived.ZModUp

namespace BEDC.Derived.LucasTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.FactorialUp
open BEDC.Derived.IntUp (natToUnary natToUnary_length)
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp

/-!
本模块导出可核验的 Lucas 路线基础面：
base-p digit fuel 展开、Pascal binomial 的 Nat 读回，以及二进制
Lucas 单步的小窗口核验。任意素数 Lucas 需要多项式 Freshman's
dream 或等价系数代数；当前文件不把该缺口包装成定理。
-/

def chooseNat : Nat -> Nat -> Nat
  | 0, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ _, 0 => 1
  | Nat.succ n, Nat.succ k => chooseNat n k + chooseNat n (Nat.succ k)

theorem chooseNat_zero_zero :
    chooseNat 0 0 = 1 := by
  rfl

theorem chooseNat_zero_succ (k : Nat) :
    chooseNat 0 (Nat.succ k) = 0 := by
  rfl

theorem chooseNat_succ_zero (n : Nat) :
    chooseNat (Nat.succ n) 0 = 1 := by
  rfl

theorem chooseNat_pascal (n k : Nat) :
    chooseNat (Nat.succ n) (Nat.succ k) =
      chooseNat n k + chooseNat n (Nat.succ k) := by
  rfl

def bedcChooseNat (n k : Nat) : Nat :=
  bwordLength (natChooseFn (natToUnary n) (natToUnary k))

theorem bedcChooseNat_pascal (n k : Nat) :
    bedcChooseNat (Nat.succ n) (Nat.succ k) =
      bedcChooseNat n k + bedcChooseNat n (Nat.succ k) := by
  unfold bedcChooseNat natChooseFn
  repeat rw [natToUnary_length]
  rfl

def baseDigitsFuel : Nat -> BHist -> BHist -> List BHist
  | 0, _p, _n => []
  | Nat.succ _fuel, _p, BHist.Empty => []
  | Nat.succ _fuel, _p, BHist.e0 _n => []
  | Nat.succ fuel, p, BHist.e1 n =>
      natModFn p (BHist.e1 n) :: baseDigitsFuel fuel p (natQuotFn p (BHist.e1 n))

def baseDigits (p n : BHist) : List BHist :=
  baseDigitsFuel (bwordLength n + 1) p n

inductive BaseDigitsFuelExpansion (p : BHist) :
    Nat -> BHist -> List BHist -> Prop where
  | out {n : BHist} :
      BaseDigitsFuelExpansion p 0 n []
  | zero {fuel : Nat} :
      BaseDigitsFuelExpansion p (Nat.succ fuel) BHist.Empty []
  | step {fuel : Nat} {n q r : BHist} {tail : List BHist} :
      NatDivRem p (BHist.e1 n) q r ->
      BaseDigitsFuelExpansion p fuel q tail ->
        BaseDigitsFuelExpansion p (Nat.succ fuel) (BHist.e1 n) (r :: tail)

def BaseDigitsExpansion (p n : BHist) (digits : List BHist) : Prop :=
  BaseDigitsFuelExpansion p (bwordLength n + 1) n digits

theorem baseDigitsFuel_expand (fuel : Nat) {p n : BHist} :
    UnaryHistory p -> UnaryHistory n -> (hsame p BHist.Empty -> False) ->
      BaseDigitsFuelExpansion p fuel n (baseDigitsFuel fuel p n) := by
  intro pUnary nUnary pNonempty
  induction fuel generalizing n with
  | zero =>
      exact BaseDigitsFuelExpansion.out
  | succ fuel ih =>
      cases n with
      | Empty =>
          exact BaseDigitsFuelExpansion.zero
      | e0 n =>
          cases nUnary
      | e1 n =>
          have divrem :
              NatDivRem p (BHist.e1 n)
                (natQuotFn p (BHist.e1 n)) (natModFn p (BHist.e1 n)) :=
            natModFn_spec pUnary nUnary pNonempty
          exact BaseDigitsFuelExpansion.step divrem
            (ih (NatDivRem_quotient_unary divrem))

theorem baseDigits_expand {p n : BHist} :
    UnaryHistory p -> UnaryHistory n -> (hsame p BHist.Empty -> False) ->
      BaseDigitsExpansion p n (baseDigits p n) := by
  intro pUnary nUnary pNonempty
  exact baseDigitsFuel_expand (bwordLength n + 1) pUnary nUnary pNonempty

def natBaseDigitsFuel : Nat -> Nat -> Nat -> List Nat
  | 0, _p, _n => []
  | Nat.succ fuel, p, n =>
      if p < 2 then
        [n]
      else
        match n with
        | 0 => []
        | Nat.succ _ =>
            (n % p) :: natBaseDigitsFuel fuel p (n / p)

def natBaseDigits (p n : Nat) : List Nat :=
  natBaseDigitsFuel (n + 1) p n

def chooseDigitProductMod (p : Nat) : List Nat -> List Nat -> Nat
  | [], [] => 1 % p
  | a :: as, [] => (chooseNat a 0 * chooseDigitProductMod p as []) % p
  | [], b :: bs => (chooseNat 0 b * chooseDigitProductMod p [] bs) % p
  | a :: as, b :: bs =>
      (chooseNat a b * chooseDigitProductMod p as bs) % p

def lucasProductMod (p m n : Nat) : Nat :=
  chooseDigitProductMod p (natBaseDigits p m) (natBaseDigits p n)

def lucasCongruenceNat (p m n : Nat) : Prop :=
  chooseNat m n % p = lucasProductMod p m n % p

def lucasStepNat (p m n : Nat) : Prop :=
  chooseNat m n % p =
    (chooseNat (m % p) (n % p) * chooseNat (m / p) (n / p)) % p

def lucasStepModTwoHoldsAt (m n : Nat) : Bool :=
  chooseNat m n % 2 ==
    (chooseNat (m % 2) (n % 2) * chooseNat (m / 2) (n / 2)) % 2

def lucasStepModTwoWindow (limit : Nat) : Bool :=
  (List.range limit).all
    (fun m =>
      (List.range limit).all
        (fun n => lucasStepModTwoHoldsAt m n))

theorem lucas_step_mod_two_small_window :
    lucasStepModTwoWindow 64 = true := by
  decide

theorem lucas_step_mod_two_5_3 :
    lucasStepNat 2 5 3 := by
  unfold lucasStepNat
  decide

theorem natBaseDigits_two_five :
    natBaseDigits 2 5 = [1, 0, 1] := by
  decide

theorem natBaseDigits_two_three :
    natBaseDigits 2 3 = [1, 1] := by
  decide

theorem bedcChooseNat_four_two :
    bedcChooseNat 4 2 = 6 := by
  rfl

theorem natChooseFn_four_two :
    natChooseFn (natToUnary 4) (natToUnary 2) = natToUnary 6 := by
  rfl

end BEDC.Derived.LucasTheoremUp
