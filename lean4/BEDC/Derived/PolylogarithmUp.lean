import BEDC.Algebra.FiniteFold
import BEDC.Derived.HarmonicUp
import BEDC.Derived.RationalUp

namespace BEDC.Derived.PolylogarithmUp

open BEDC.Derived.RationalUp

abbrev Rat : Type :=
  RatNum

def ratPow (x : Rat) : Nat -> Rat
  | 0 => ratOne
  | Nat.succ n => ratMul (ratPow x n) x

def reciprocalSuccPow (k : Nat) : Nat -> Rat
  | 0 => ratOne
  | Nat.succ s =>
      ratMul (reciprocalSuccPow k s)
        (BEDC.Derived.HarmonicUp.oneOverNatSucc k)

def polylogTerm (s : Nat) (x : Rat) (k : Nat) : Rat :=
  ratMul (ratPow x (Nat.succ k)) (reciprocalSuccPow k s)

def polylogTerms (s : Nat) (x : Rat) : Nat -> List Rat
  | 0 => []
  | Nat.succ n => polylogTerms s x n ++ [polylogTerm s x n]

def polylogTrunc (s : Nat) (x : Rat) : Nat -> Rat
  | 0 => ratZero
  | Nat.succ n => ratAdd (polylogTrunc s x n) (polylogTerm s x n)

def geometricTrunc (x : Rat) : Nat -> Rat
  | 0 => ratZero
  | Nat.succ n => ratAdd (geometricTrunc x n) (ratPow x (Nat.succ n))

def zetaTerm (s : Nat) (k : Nat) : Rat :=
  reciprocalSuccPow k s

def zetaTrunc (s : Nat) : Nat -> Rat
  | 0 => ratZero
  | Nat.succ n => ratAdd (zetaTrunc s n) (zetaTerm s n)

def negLogOneMinusTerm (x : Rat) (k : Nat) : Rat :=
  ratMul (ratPow x (Nat.succ k))
    (BEDC.Derived.HarmonicUp.oneOverNatSucc k)

def negLogOneMinusTrunc (x : Rat) : Nat -> Rat
  | 0 => ratZero
  | Nat.succ n => ratAdd (negLogOneMinusTrunc x n) (negLogOneMinusTerm x n)

def positiveIndexRat (k : Nat) : Rat :=
  ratInvApart (BEDC.Derived.HarmonicUp.oneOverNatSucc k)
    (BEDC.Derived.HarmonicUp.oneOverNatSucc_positive k).right

def xDdxPolylogTerm (s : Nat) (x : Rat) (k : Nat) : Rat :=
  ratMul (ratPow x (Nat.succ k))
    (ratMul (positiveIndexRat k) (reciprocalSuccPow k (Nat.succ s)))

def xDdxPolylogTrunc (s : Nat) (x : Rat) : Nat -> Rat
  | 0 => ratZero
  | Nat.succ n => ratAdd (xDdxPolylogTrunc s x n) (xDdxPolylogTerm s x n)

theorem ratPow_zero (x : Rat) :
    RatEq (ratPow x 0) ratOne := by
  exact RatEq_refl ratOne

theorem ratPow_succ (x : Rat) (n : Nat) :
    RatEq (ratPow x (Nat.succ n)) (ratMul (ratPow x n) x) := by
  exact RatEq_refl (ratPow x (Nat.succ n))

theorem ratPow_one (n : Nat) :
    RatEq (ratPow ratOne n) ratOne := by
  induction n with
  | zero =>
      exact RatEq_refl ratOne
  | succ n ih =>
      exact RatEq_trans (ratPow ratOne (Nat.succ n))
        (ratMul ratOne ratOne) ratOne
        (ratMul_respects ih (RatEq_refl ratOne))
        (ratMul_one_right ratOne)

theorem reciprocalSuccPow_zero (k : Nat) :
    RatEq (reciprocalSuccPow k 0) ratOne := by
  exact RatEq_refl ratOne

theorem reciprocalSuccPow_succ (k s : Nat) :
    RatEq (reciprocalSuccPow k (Nat.succ s))
      (ratMul (reciprocalSuccPow k s)
        (BEDC.Derived.HarmonicUp.oneOverNatSucc k)) := by
  exact RatEq_refl (reciprocalSuccPow k (Nat.succ s))

theorem reciprocalSuccPow_one (k : Nat) :
    RatEq (reciprocalSuccPow k 1)
      (BEDC.Derived.HarmonicUp.oneOverNatSucc k) := by
  exact ratOne_mul_left (BEDC.Derived.HarmonicUp.oneOverNatSucc k)

theorem polylogTrunc_zero (s : Nat) (x : Rat) :
    RatEq (polylogTrunc s x 0) ratZero := by
  exact RatEq_refl ratZero

theorem polylogTrunc_succ (s : Nat) (x : Rat) (n : Nat) :
    RatEq (polylogTrunc s x (Nat.succ n))
      (ratAdd (polylogTrunc s x n) (polylogTerm s x n)) := by
  exact RatEq_refl (polylogTrunc s x (Nat.succ n))

theorem polylogTerms_zero (s : Nat) (x : Rat) :
    polylogTerms s x 0 = [] := by
  rfl

theorem polylogTerms_succ (s : Nat) (x : Rat) (n : Nat) :
    polylogTerms s x (Nat.succ n) =
      polylogTerms s x n ++ [polylogTerm s x n] := by
  rfl

theorem polylogTerm_weight_zero (x : Rat) (k : Nat) :
    RatEq (polylogTerm 0 x k) (ratPow x (Nat.succ k)) := by
  exact ratMul_one_right (ratPow x (Nat.succ k))

theorem polylogTrunc_weight_zero (x : Rat) (n : Nat) :
    RatEq (polylogTrunc 0 x n) (geometricTrunc x n) := by
  induction n with
  | zero =>
      exact RatEq_refl ratZero
  | succ n ih =>
      exact ratAdd_respects ih (polylogTerm_weight_zero x n)

theorem polylogTerm_at_one (s k : Nat) :
    RatEq (polylogTerm s ratOne k) (zetaTerm s k) := by
  exact RatEq_trans (polylogTerm s ratOne k)
    (ratMul ratOne (zetaTerm s k)) (zetaTerm s k)
    (ratMul_respects (ratPow_one (Nat.succ k)) (RatEq_refl (zetaTerm s k)))
    (ratOne_mul_left (zetaTerm s k))

theorem polylogTrunc_at_one (s n : Nat) :
    RatEq (polylogTrunc s ratOne n) (zetaTrunc s n) := by
  induction n with
  | zero =>
      exact RatEq_refl ratZero
  | succ n ih =>
      exact ratAdd_respects ih (polylogTerm_at_one s n)

theorem polylogTerm_one_eq_negLogTerm (x : Rat) (k : Nat) :
    RatEq (polylogTerm 1 x k) (negLogOneMinusTerm x k) := by
  exact ratMul_respects (RatEq_refl (ratPow x (Nat.succ k)))
    (reciprocalSuccPow_one k)

theorem polylogTrunc_one_eq_negLogTrunc (x : Rat) (n : Nat) :
    RatEq (polylogTrunc 1 x n) (negLogOneMinusTrunc x n) := by
  induction n with
  | zero =>
      exact RatEq_refl ratZero
  | succ n ih =>
      exact ratAdd_respects ih (polylogTerm_one_eq_negLogTerm x n)

theorem oneOverNatSucc_mul_positiveIndexRat (k : Nat) :
    RatEq
      (ratMul (BEDC.Derived.HarmonicUp.oneOverNatSucc k) (positiveIndexRat k))
      ratOne := by
  exact ratInvApart_mul (BEDC.Derived.HarmonicUp.oneOverNatSucc k)
    (BEDC.Derived.HarmonicUp.oneOverNatSucc_positive k).right

theorem positiveIndexRat_mul_oneOverNatSucc (k : Nat) :
    RatEq
      (ratMul (positiveIndexRat k) (BEDC.Derived.HarmonicUp.oneOverNatSucc k))
      ratOne := by
  exact RatEq_trans
    (ratMul (positiveIndexRat k) (BEDC.Derived.HarmonicUp.oneOverNatSucc k))
    (ratMul (BEDC.Derived.HarmonicUp.oneOverNatSucc k) (positiveIndexRat k))
    ratOne
    (ratMul_comm (positiveIndexRat k) (BEDC.Derived.HarmonicUp.oneOverNatSucc k))
    (oneOverNatSucc_mul_positiveIndexRat k)

theorem positiveIndexRat_mul_reciprocalSuccPow_succ (k s : Nat) :
    RatEq (ratMul (positiveIndexRat k) (reciprocalSuccPow k (Nat.succ s)))
      (reciprocalSuccPow k s) := by
  let idx := positiveIndexRat k
  let coeff := reciprocalSuccPow k s
  let recip := BEDC.Derived.HarmonicUp.oneOverNatSucc k
  have inverse : RatEq (ratMul idx recip) ratOne := by
    unfold idx recip
    exact positiveIndexRat_mul_oneOverNatSucc k
  have assocLeft :
      RatEq (ratMul idx (ratMul coeff recip))
        (ratMul (ratMul idx coeff) recip) :=
    RatEq_symm (ratMul_assoc idx coeff recip)
  have swapCoeff :
      RatEq (ratMul (ratMul idx coeff) recip)
        (ratMul (ratMul coeff idx) recip) :=
    ratMul_respects (ratMul_comm idx coeff) (RatEq_refl recip)
  have assocRight :
      RatEq (ratMul (ratMul coeff idx) recip)
        (ratMul coeff (ratMul idx recip)) :=
    ratMul_assoc coeff idx recip
  have consume :
      RatEq (ratMul coeff (ratMul idx recip)) (ratMul coeff ratOne) :=
    ratMul_respects (RatEq_refl coeff) inverse
  have finish :
      RatEq (ratMul coeff ratOne) coeff :=
    ratMul_one_right coeff
  exact RatEq_trans (ratMul idx (reciprocalSuccPow k (Nat.succ s)))
    (ratMul idx (ratMul coeff recip)) coeff
    (RatEq_refl (ratMul idx (reciprocalSuccPow k (Nat.succ s))))
    (RatEq_trans (ratMul idx (ratMul coeff recip))
      (ratMul (ratMul idx coeff) recip) coeff assocLeft
      (RatEq_trans (ratMul (ratMul idx coeff) recip)
        (ratMul (ratMul coeff idx) recip) coeff swapCoeff
        (RatEq_trans (ratMul (ratMul coeff idx) recip)
          (ratMul coeff (ratMul idx recip)) coeff assocRight
          (RatEq_trans (ratMul coeff (ratMul idx recip))
            (ratMul coeff ratOne) coeff consume finish))))

theorem xDdxPolylogTerm_lowering (s : Nat) (x : Rat) (k : Nat) :
    RatEq (xDdxPolylogTerm s x k) (polylogTerm s x k) := by
  exact ratMul_respects (RatEq_refl (ratPow x (Nat.succ k)))
    (positiveIndexRat_mul_reciprocalSuccPow_succ k s)

theorem xDdxPolylogTrunc_lowering (s : Nat) (x : Rat) (n : Nat) :
    RatEq (xDdxPolylogTrunc s x n) (polylogTrunc s x n) := by
  induction n with
  | zero =>
      exact RatEq_refl ratZero
  | succ n ih =>
      exact ratAdd_respects ih (xDdxPolylogTerm_lowering s x n)

theorem PolylogarithmUp_constructive_export (x : Rat) (s n : Nat) :
    RatEq (polylogTrunc s ratOne n) (zetaTrunc s n) ∧
      RatEq (polylogTrunc 1 x n) (negLogOneMinusTrunc x n) ∧
        RatEq (xDdxPolylogTrunc s x n) (polylogTrunc s x n) ∧
          RatEq (polylogTrunc 0 x n) (geometricTrunc x n) := by
  constructor
  · exact polylogTrunc_at_one s n
  · constructor
    · exact polylogTrunc_one_eq_negLogTrunc x n
    · constructor
      · exact xDdxPolylogTrunc_lowering s x n
      · exact polylogTrunc_weight_zero x n

end BEDC.Derived.PolylogarithmUp
