import BEDC.Derived.VonStaudtClausenUp

namespace BEDC.Derived.KummerCongruenceUp

open BEDC.Derived.BernoulliUp
open BEDC.Derived.VonStaudtClausenUp

/-!
本文件只导出可由现有 BEDC 原语核验的小窗口 Kummer 同余。
一般全称 Kummer 定理需要更强的 Bernoulli 递推和 p-adic 传输库支撑,
这里保持为可检查的谓词接口和小素数真证明。
-/

def intModNat (z : Int) (p : Nat) : Nat :=
  match p with
  | 0 => 0
  | Nat.succ q =>
      match z with
      | Int.ofNat n => n % Nat.succ q
      | Int.negSucc n => (Nat.succ q - (Nat.succ n % Nat.succ q)) % Nat.succ q

def rawRatCrossModEq (p : Nat) (x y : RawRat) : Prop :=
  intModNat (x.num * Int.ofNat y.den) p =
    intModNat (y.num * Int.ofNat x.den) p

def rawRatDenUnitMod (p : Nat) (x : RawRat) : Prop :=
  x.den % p ≠ 0

def rawRatCongruentMod (p : Nat) (x y : RawRat) : Prop :=
  rawRatDenUnitMod p x ∧ rawRatDenUnitMod p y ∧ rawRatCrossModEq p x y

def rawRatDivNat (x : RawRat) (n : Nat) : RawRat :=
  rawScaleDen x (n - 1)

def rawBernoulliOverIndex (n : Nat) : RawRat :=
  rawRatDivNat (rawBernoulli n) n

def lucasIndexCongruent (p m n : Nat) : Prop :=
  m % (p - 1) = n % (p - 1)

def lucasIndexNonzero (p m : Nat) : Prop :=
  m % (p - 1) ≠ 0

structure KummerInput where
  p : Nat
  m : Nat
  n : Nat
  p_prime : BEDC.Derived.PrimeUp.NatPrime
    (BEDC.Derived.IntUp.natToUnary p)
  index_same : lucasIndexCongruent p m n
  m_nonzero : lucasIndexNonzero p m
  n_nonzero : lucasIndexNonzero p n

def kummerCongruenceAt (p m n : Nat) : Prop :=
  rawRatCongruentMod p (rawBernoulliOverIndex m) (rawBernoulliOverIndex n)

def KummerCongruenceStatement (input : KummerInput) : Prop :=
  kummerCongruenceAt input.p input.m input.n

def vscCandidateExcludedForIndex (p k : Nat) : Prop :=
  (clausePrimeCandidates k).count p = 0

def vscSupportsKummerAt (p m n : Nat) : Prop :=
  rawBernoulliDenominatorMatchesClausenAt (m / 2) ∧
    rawBernoulliDenominatorMatchesClausenAt (n / 2) ∧
      vscCandidateExcludedForIndex p (m / 2) ∧
        vscCandidateExcludedForIndex p (n / 2) ∧
          rawRatDenUnitMod p (rawBernoulliOverIndex m) ∧
            rawRatDenUnitMod p (rawBernoulliOverIndex n)

theorem rawBernoulli_eight_value :
    rawBernoulli 8 = { num := -1, denMinusOne := 29 } := by
  rfl

theorem rawBernoulliOverIndex_two_value :
    rawBernoulliOverIndex 2 = { num := 1, denMinusOne := 11 } := by
  rfl

theorem rawBernoulliOverIndex_six_value :
    rawBernoulliOverIndex 6 = { num := 1, denMinusOne := 251 } := by
  rfl

theorem rawBernoulliOverIndex_eight_value :
    rawBernoulliOverIndex 8 = { num := -1, denMinusOne := 239 } := by
  rfl

theorem clausePrimeCandidates_four :
    clausePrimeCandidates 4 = [2, 3, 5] := by
  rfl

theorem clauseDenominatorProductNat_four :
    clauseDenominatorProductNat 4 = 30 := by
  rfl

theorem rawBernoulliDenominator_eight :
    rawBernoulliDenominator 8 = 30 := by
  rfl

theorem rawBernoulli_eight_denominator_matches_clausen :
    rawBernoulliDenominatorMatchesClausenAt 4 := by
  rfl

def kummerInputFiveTwoSix : KummerInput where
  p := 5
  m := 2
  n := 6
  p_prime := by
    exact NatFive_prime
  index_same := by
    rfl
  m_nonzero := by
    unfold lucasIndexNonzero
    decide
  n_nonzero := by
    unfold lucasIndexNonzero
    decide

def kummerInputSevenTwoEight : KummerInput where
  p := 7
  m := 2
  n := 8
  p_prime := by
    exact NatSeven_prime
  index_same := by
    rfl
  m_nonzero := by
    unfold lucasIndexNonzero
    decide
  n_nonzero := by
    unfold lucasIndexNonzero
    decide

theorem kummer_mod_five_two_six :
    KummerCongruenceStatement kummerInputFiveTwoSix := by
  unfold KummerCongruenceStatement kummerCongruenceAt rawRatCongruentMod
  unfold rawRatDenUnitMod rawRatCrossModEq
  decide

theorem kummer_mod_seven_two_eight :
    KummerCongruenceStatement kummerInputSevenTwoEight := by
  unfold KummerCongruenceStatement kummerCongruenceAt rawRatCongruentMod
  unfold rawRatDenUnitMod rawRatCrossModEq
  decide

theorem vsc_supports_kummer_mod_five_two_six :
    vscSupportsKummerAt 5 2 6 := by
  constructor
  · exact rawBernoulli_two_denominator_matches_clausen
  · constructor
    · exact rawBernoulli_six_denominator_matches_clausen
    · constructor
      · unfold vscCandidateExcludedForIndex
        decide
      · constructor
        · unfold vscCandidateExcludedForIndex
          decide
        · constructor
          · unfold rawRatDenUnitMod
            decide
          · unfold rawRatDenUnitMod
            decide

theorem vsc_supports_kummer_mod_seven_two_eight :
    vscSupportsKummerAt 7 2 8 := by
  constructor
  · exact rawBernoulli_two_denominator_matches_clausen
  · constructor
    · exact rawBernoulli_eight_denominator_matches_clausen
    · constructor
      · unfold vscCandidateExcludedForIndex
        decide
      · constructor
        · unfold vscCandidateExcludedForIndex
          decide
        · constructor
          · unfold rawRatDenUnitMod
            decide
          · unfold rawRatDenUnitMod
            decide

theorem small_kummer_vsc_window :
    KummerCongruenceStatement kummerInputFiveTwoSix ∧
      vscSupportsKummerAt 5 2 6 ∧
        KummerCongruenceStatement kummerInputSevenTwoEight ∧
          vscSupportsKummerAt 7 2 8 := by
  exact ⟨kummer_mod_five_two_six,
    vsc_supports_kummer_mod_five_two_six,
    kummer_mod_seven_two_eight,
    vsc_supports_kummer_mod_seven_two_eight⟩

end BEDC.Derived.KummerCongruenceUp
