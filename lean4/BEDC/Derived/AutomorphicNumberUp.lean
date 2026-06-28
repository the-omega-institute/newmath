import BEDC.Derived.IntUp.Arithmetic
import BEDC.Derived.NatUp
import BEDC.Derived.ZModUp

set_option maxRecDepth 2000

namespace BEDC.Derived.AutomorphicNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp (natToUnary natToUnary_unary)
open BEDC.Derived.ZModUp

/-!
  Automorphic 数在 Nat 层导出为模 $10^k$ 的 idempotent。
  CRT 分类只给出有限 witness 数据；本文件证明其中的可计算锚点。
-/

def tenPow (k : Nat) : Nat :=
  10 ^ k

def powTwoFiveModulus (k : Nat) : Nat :=
  2 ^ k * 5 ^ k

def idempotentMod (m n : Nat) : Prop :=
  (n * n) % m = n % m

def automorphicNat (k n : Nat) : Prop :=
  idempotentMod (tenPow k) n

def automorphicHist (k n : Nat) : Prop :=
  automorphicNat k n ∧
    UnaryHistory (natToUnary k) ∧ UnaryHistory (natToUnary n)

def AutomorphicResidue (k : Nat) : Type :=
  ZMod (natToUnary (tenPow k))

def automorphicResidue (k n : Nat)
    (modulusNonempty : hsame (natToUnary (tenPow k)) BHist.Empty -> False) :
    AutomorphicResidue k :=
  zmodFromNat (natToUnary (tenPow k))
    (natToUnary_unary (tenPow k))
    modulusNonempty
    (natToUnary n)
    (natToUnary_unary n)

def automorphicDigitRead (digits : List Nat) : Nat :=
  digits.foldr (fun digit acc => digit + 10 * acc) 0

def automorphicDigitsNat (k : Nat) (digits : List Nat) : Prop :=
  automorphicNat k (automorphicDigitRead digits)

inductive AutomorphicBranch where
  | zeroOne
  | fiveAdic
  | sixAdic
  deriving DecidableEq, Repr

structure AutomorphicFamily where
  branch : AutomorphicBranch
  level : Nat
  value : Nat
  certified : automorphicNat level value

def fivePowerTowerValue (k : Nat) : Nat :=
  5 ^ (2 ^ k)

def sixPowerTowerValue (k : Nat) : Nat :=
  6 ^ (5 ^ k)

def fivePowerTowerFamily (k : Nat) (value : Nat)
    (certified : automorphicNat k value) : AutomorphicFamily where
  branch := AutomorphicBranch.fiveAdic
  level := k
  value := value
  certified := certified

def sixPowerTowerFamily (k : Nat) (value : Nat)
    (certified : automorphicNat k value) : AutomorphicFamily where
  branch := AutomorphicBranch.sixAdic
  level := k
  value := value
  certified := certified

structure CRTIdempotentWitness where
  level : Nat
  value : Nat
  moduloTwo : idempotentMod (2 ^ level) value
  moduloFive : idempotentMod (5 ^ level) value
  moduloTen : automorphicNat level value

theorem automorphic_idempotent {k n : Nat} :
    automorphicNat k n -> idempotentMod (tenPow k) n := by
  intro certified
  exact certified

theorem automorphicHist_idempotent {k n : Nat} :
    automorphicHist k n -> idempotentMod (tenPow k) n := by
  intro certified
  exact certified.left

theorem automorphicHist_unary_index {k n : Nat} :
    automorphicHist k n -> UnaryHistory (natToUnary k) := by
  intro certified
  exact certified.right.left

theorem automorphicHist_unary_value {k n : Nat} :
    automorphicHist k n -> UnaryHistory (natToUnary n) := by
  intro certified
  exact certified.right.right

theorem powTwoFiveModulus_zero :
    powTwoFiveModulus 0 = tenPow 0 := rfl

theorem powTwoFiveModulus_one :
    powTwoFiveModulus 1 = tenPow 1 := rfl

theorem powTwoFiveModulus_two :
    powTwoFiveModulus 2 = tenPow 2 := rfl

theorem powTwoFiveModulus_three :
    powTwoFiveModulus 3 = tenPow 3 := rfl

theorem automorphicNat_five :
    automorphicNat 1 5 := rfl

theorem automorphicNat_six :
    automorphicNat 1 6 := rfl

theorem automorphicNat_twentyFive :
    automorphicNat 2 25 := rfl

theorem automorphicNat_seventySix :
    automorphicNat 2 76 := rfl

theorem automorphicNat_threeSeventySix :
    automorphicNat 3 376 := rfl

theorem automorphicNat_sixTwentyFive :
    automorphicNat 3 625 := rfl

theorem automorphicHist_five :
    automorphicHist 1 5 := by
  exact ⟨automorphicNat_five, natToUnary_unary 1, natToUnary_unary 5⟩

theorem automorphicHist_six :
    automorphicHist 1 6 := by
  exact ⟨automorphicNat_six, natToUnary_unary 1, natToUnary_unary 6⟩

theorem automorphicHist_twentyFive :
    automorphicHist 2 25 := by
  exact ⟨automorphicNat_twentyFive, natToUnary_unary 2, natToUnary_unary 25⟩

theorem automorphicHist_seventySix :
    automorphicHist 2 76 := by
  exact ⟨automorphicNat_seventySix, natToUnary_unary 2, natToUnary_unary 76⟩

theorem automorphicHist_threeSeventySix :
    automorphicHist 3 376 := by
  exact ⟨automorphicNat_threeSeventySix, natToUnary_unary 3, natToUnary_unary 376⟩

theorem automorphicHist_sixTwentyFive :
    automorphicHist 3 625 := by
  exact ⟨automorphicNat_sixTwentyFive, natToUnary_unary 3, natToUnary_unary 625⟩

theorem automorphicDigitRead_five :
    automorphicDigitRead [5] = 5 := rfl

theorem automorphicDigitRead_six :
    automorphicDigitRead [6] = 6 := rfl

theorem automorphicDigitRead_twentyFive :
    automorphicDigitRead [5, 2] = 25 := rfl

theorem automorphicDigitRead_seventySix :
    automorphicDigitRead [6, 7] = 76 := rfl

theorem automorphicDigitRead_threeSeventySix :
    automorphicDigitRead [6, 7, 3] = 376 := rfl

theorem automorphicDigitRead_sixTwentyFive :
    automorphicDigitRead [5, 2, 6] = 625 := rfl

theorem automorphicDigitsNat_five :
    automorphicDigitsNat 1 [5] := rfl

theorem automorphicDigitsNat_six :
    automorphicDigitsNat 1 [6] := rfl

theorem automorphicDigitsNat_twentyFive :
    automorphicDigitsNat 2 [5, 2] := rfl

theorem automorphicDigitsNat_seventySix :
    automorphicDigitsNat 2 [6, 7] := rfl

theorem automorphicDigitsNat_threeSeventySix :
    automorphicDigitsNat 3 [6, 7, 3] := rfl

theorem automorphicDigitsNat_sixTwentyFive :
    automorphicDigitsNat 3 [5, 2, 6] := rfl

theorem fivePowerTowerValue_zero :
    fivePowerTowerValue 0 = 5 := rfl

theorem sixPowerTowerValue_zero :
    sixPowerTowerValue 0 = 6 := rfl

def automorphicFamily_five :
    AutomorphicFamily :=
  fivePowerTowerFamily 1 5 automorphicNat_five

def automorphicFamily_six :
    AutomorphicFamily :=
  sixPowerTowerFamily 1 6 automorphicNat_six

def automorphicFamily_twentyFive :
    AutomorphicFamily :=
  fivePowerTowerFamily 2 25 automorphicNat_twentyFive

def automorphicFamily_seventySix :
    AutomorphicFamily :=
  sixPowerTowerFamily 2 76 automorphicNat_seventySix

def automorphicFamily_threeSeventySix :
    AutomorphicFamily :=
  sixPowerTowerFamily 3 376 automorphicNat_threeSeventySix

def automorphicFamily_sixTwentyFive :
    AutomorphicFamily :=
  fivePowerTowerFamily 3 625 automorphicNat_sixTwentyFive

def crtWitness_five : CRTIdempotentWitness where
  level := 1
  value := 5
  moduloTwo := rfl
  moduloFive := rfl
  moduloTen := automorphicNat_five

def crtWitness_six : CRTIdempotentWitness where
  level := 1
  value := 6
  moduloTwo := rfl
  moduloFive := rfl
  moduloTen := automorphicNat_six

def crtWitness_twentyFive : CRTIdempotentWitness where
  level := 2
  value := 25
  moduloTwo := rfl
  moduloFive := rfl
  moduloTen := automorphicNat_twentyFive

def crtWitness_seventySix : CRTIdempotentWitness where
  level := 2
  value := 76
  moduloTwo := rfl
  moduloFive := rfl
  moduloTen := automorphicNat_seventySix

def crtWitness_threeSeventySix : CRTIdempotentWitness where
  level := 3
  value := 376
  moduloTwo := rfl
  moduloFive := rfl
  moduloTen := automorphicNat_threeSeventySix

def crtWitness_sixTwentyFive : CRTIdempotentWitness where
  level := 3
  value := 625
  moduloTwo := rfl
  moduloFive := rfl
  moduloTen := automorphicNat_sixTwentyFive

theorem crtWitness_five_idempotent :
    automorphicNat crtWitness_five.level crtWitness_five.value :=
  crtWitness_five.moduloTen

theorem crtWitness_six_idempotent :
    automorphicNat crtWitness_six.level crtWitness_six.value :=
  crtWitness_six.moduloTen

theorem crtWitness_twentyFive_idempotent :
    automorphicNat crtWitness_twentyFive.level crtWitness_twentyFive.value :=
  crtWitness_twentyFive.moduloTen

theorem crtWitness_seventySix_idempotent :
    automorphicNat crtWitness_seventySix.level crtWitness_seventySix.value :=
  crtWitness_seventySix.moduloTen

theorem crtWitness_threeSeventySix_idempotent :
    automorphicNat crtWitness_threeSeventySix.level crtWitness_threeSeventySix.value :=
  crtWitness_threeSeventySix.moduloTen

theorem crtWitness_sixTwentyFive_idempotent :
    automorphicNat crtWitness_sixTwentyFive.level crtWitness_sixTwentyFive.value :=
  crtWitness_sixTwentyFive.moduloTen

theorem automorphicSmallValues :
    automorphicNat 1 5 ∧ automorphicNat 1 6 ∧ automorphicNat 2 25 ∧
      automorphicNat 2 76 ∧ automorphicNat 3 376 ∧ automorphicNat 3 625 := by
  exact
    ⟨automorphicNat_five, automorphicNat_six, automorphicNat_twentyFive,
      automorphicNat_seventySix, automorphicNat_threeSeventySix,
      automorphicNat_sixTwentyFive⟩

theorem AutomorphicNumberUp_constructive_export :
    automorphicNat 1 5 ∧ automorphicNat 1 6 ∧ automorphicNat 2 25 ∧
      automorphicNat 2 76 ∧ automorphicNat 3 376 ∧ automorphicNat 3 625 ∧
        automorphicDigitsNat 1 [5] ∧ automorphicDigitsNat 1 [6] ∧
          automorphicDigitsNat 2 [5, 2] ∧ automorphicDigitsNat 2 [6, 7] ∧
            automorphicDigitsNat 3 [6, 7, 3] ∧
              automorphicDigitsNat 3 [5, 2, 6] := by
  exact
    ⟨automorphicNat_five, automorphicNat_six, automorphicNat_twentyFive,
      automorphicNat_seventySix, automorphicNat_threeSeventySix,
      automorphicNat_sixTwentyFive, automorphicDigitsNat_five,
      automorphicDigitsNat_six, automorphicDigitsNat_twentyFive,
      automorphicDigitsNat_seventySix, automorphicDigitsNat_threeSeventySix,
      automorphicDigitsNat_sixTwentyFive⟩

end BEDC.Derived.AutomorphicNumberUp
