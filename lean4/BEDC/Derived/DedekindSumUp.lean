import BEDC.Derived.RationalUp.MetricOrder
import BEDC.Derived.GcdUp
import BEDC.Algebra.FiniteFold

namespace BEDC.Derived.DedekindSumUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp (natToUnary natToUnary_unary)
open BEDC.Derived.RationalUp

private def unaryHistoryDecidableLocal : (h : BHist) -> Decidable (UnaryHistory h)
  | BHist.Empty => isTrue True.intro
  | BHist.e0 _ => isFalse (fun h => h)
  | BHist.e1 h => unaryHistoryDecidableLocal h

private instance (h : BHist) : Decidable (UnaryHistory h) :=
  unaryHistoryDecidableLocal h

private instance (h k : BHist) : Decidable (hsame h k) := by
  unfold hsame
  infer_instance

private instance (x : BHist × BHist) : Decidable (BEDC.Derived.IntUp.IntPairCarrier x.1 x.2) := by
  unfold BEDC.Derived.IntUp.IntPairCarrier
  infer_instance

private instance (x y : BHist × BHist) :
    Decidable (BEDC.Derived.IntUp.IntPairClassifier x y) := by
  unfold BEDC.Derived.IntUp.IntPairClassifier
  infer_instance

private instance (x y : BEDC.Derived.PrimeUp.IntegerUp) :
    Decidable (BEDC.Derived.RationalUp.IntEq x y) := by
  unfold BEDC.Derived.RationalUp.IntEq
  infer_instance

private instance (x y : RatNum) : Decidable (RatEq x y) := by
  unfold RatEq
  infer_instance

structure PositiveNat where
  val : Nat
  pos : 0 < val

def positiveOne : PositiveNat :=
  { val := 1, pos := Nat.succ_pos 0 }

def positiveTwo : PositiveNat :=
  { val := 2, pos := Nat.succ_pos 1 }

def positiveThree : PositiveNat :=
  { val := 3, pos := Nat.succ_pos 2 }

def positiveFour : PositiveNat :=
  { val := 4, pos := Nat.succ_pos 3 }

private theorem natToUnary_one_left_cont (n : Nat) :
    BEDC.FKernel.Cont.Cont BEDC.Derived.PadicUp.NatOne (natToUnary n)
      (natToUnary (Nat.succ n)) := by
  induction n with
  | zero =>
      rfl
  | succ _ ih =>
      change BHist.e1 (natToUnary _) =
        BHist.e1
          (BEDC.FKernel.Cont.append BEDC.Derived.PadicUp.NatOne _)
      exact congrArg BHist.e1 ih

def positiveDenPos (n : PositiveNat) :
    BEDC.Derived.NatUp.NatUnaryStrictPrefix
        BEDC.Derived.PadicUp.NatOne (natToUnary n.val) ∨
      hsame (natToUnary n.val) BEDC.Derived.PadicUp.NatOne := by
  cases n with
  | mk val pos =>
      cases val with
      | zero =>
          cases pos
      | succ val =>
          cases val with
          | zero =>
              exact Or.inr rfl
          | succ val =>
              exact Or.inl
                ⟨natToUnary (Nat.succ val), natToUnary_unary (Nat.succ val),
                  (fun empty => by cases empty),
                  natToUnary_one_left_cont (Nat.succ val)⟩

def ratOfSignedNatOver (sign : BMark) (num : Nat) (den : PositiveNat) : RatNum :=
  { num := intOfNatWithSign sign (natToUnary num) (natToUnary_unary num)
    den := natToUnary den.val
    den_pos := positiveDenPos den }

def ratOfNatOver (num : Nat) (den : PositiveNat) : RatNum :=
  ratOfSignedNatOver BMark.b0 num den

def ratOfUnaryOver (num : BHist) (numUnary : UnaryHistory num)
    (den : PositiveNat) : RatNum :=
  { num :=
      intOfNat num numUnary
    den := natToUnary den.val
    den_pos := positiveDenPos den }

def ratHalf : RatNum :=
  ratOfNatOver 1 { val := 2, pos := Nat.succ_pos 1 }

def ratQuarter : RatNum :=
  ratOfNatOver 1 { val := 4, pos := Nat.succ_pos 3 }

def ratTwelve : PositiveNat :=
  { val := 12, pos := Nat.succ_pos 11 }

def ratNegQuarter : RatNum :=
  ratOfSignedNatOver BMark.b1 1 { val := 4, pos := Nat.succ_pos 3 }

def positiveProduct (h k : PositiveNat) : PositiveNat :=
  { val := h.val * k.val, pos := Nat.mul_pos h.pos k.pos }

def sawtoothNatOver (num : Nat) (den : PositiveNat) : RatNum :=
  let rem := BEDC.Derived.PadicUp.natModFn (natToUnary den.val) (natToUnary num)
  have remUnary : UnaryHistory rem :=
    BEDC.Derived.PadicUp.natModFn_unary_all (natToUnary den.val) (natToUnary num)
  match rem with
  | BHist.Empty => ratZero
  | BHist.e0 _tail => False.elim (unary_no_zero_extension remUnary)
  | BHist.e1 _tail => ratSub (ratOfUnaryOver (BHist.e1 _tail) remUnary den) ratHalf

def dedekindIndexList (k : PositiveNat) : List Nat :=
  (List.range (k.val - 1)).map (fun n => n + 1)

def dedekindTerm (h k : PositiveNat) (i : Nat) : RatNum :=
  ratMul (sawtoothNatOver i k) (sawtoothNatOver (h.val * i) k)

def ratListSum : List RatNum -> RatNum
  | [] => ratZero
  | x :: xs => ratAdd x (ratListSum xs)

def dedekindSum (h k : PositiveNat) : RatNum :=
  ratListSum ((dedekindIndexList k).map (dedekindTerm h k))

def s (h k : PositiveNat) : RatNum :=
  dedekindSum h k

def dedekindReciprocityRhs (h k : PositiveNat) : RatNum :=
  ratAdd ratNegQuarter
    (ratMul
      (ratAdd
        (ratAdd (ratOfNatOver h.val k) (ratOfNatOver k.val h))
        (ratOfNatOver 1 (positiveProduct h k)))
      (ratOfNatOver 1 ratTwelve))

def dedekindSumOneClosedFormulaRhs (k : PositiveNat) : RatNum :=
  ratOfNatOver ((k.val - 1) * (k.val - 2)) (positiveProduct ratTwelve k)

theorem dedekindIndexList_one :
    dedekindIndexList positiveOne = [] := by
  rfl

theorem s_eq_dedekindSum (h k : PositiveNat) :
    RatEq (s h k) (dedekindSum h k) := by
  exact RatEq_refl (dedekindSum h k)

theorem dedekindSum_one_one :
    RatEq (dedekindSum positiveOne positiveOne) ratZero := by
  exact RatEq_refl ratZero

theorem dedekindSum_one_one_double_zero :
    RatEq
      (ratAdd (dedekindSum positiveOne positiveOne)
        (dedekindSum positiveOne positiveOne))
      (ratAdd ratZero ratZero) := by
  exact RatEq_refl (ratAdd ratZero ratZero)

theorem dedekindSum_one_one_closed_formula :
    RatEq (dedekindSum positiveOne positiveOne)
      (dedekindSumOneClosedFormulaRhs positiveOne) := by
  decide

theorem dedekindSum_one_two_closed_formula :
    RatEq (dedekindSum positiveOne positiveTwo)
      (dedekindSumOneClosedFormulaRhs positiveTwo) := by
  decide

theorem dedekindSum_one_two_value :
    RatEq (dedekindSum positiveOne positiveTwo) ratZero := by
  decide

theorem dedekindReciprocity_one_one_rhs_zero :
    RatEq (dedekindReciprocityRhs positiveOne positiveOne) ratZero := by
  decide

theorem dedekindReciprocity_one_one_instance :
    RatEq
      (ratAdd (dedekindSum positiveOne positiveOne)
        (dedekindSum positiveOne positiveOne))
      (dedekindReciprocityRhs positiveOne positiveOne) := by
  decide

end BEDC.Derived.DedekindSumUp
