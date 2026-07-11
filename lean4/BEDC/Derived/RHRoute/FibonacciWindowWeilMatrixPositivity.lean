import BEDC.Derived.RHRoute.IntervalMatrixPSD
import BEDC.Real.RatNumLogEnclosure

set_option maxHeartbeats 12000000
set_option maxRecDepth 4096

/-!
# Fibonacci-window Weil matrix positivity

This file certifies positive semidefiniteness for the rational 3 by 3
approximant of the Weil explicit-formula quadratic form on the degree-3
Fibonacci-hat test window.  The entries are scaled by 10^9 and come from
the von Mangoldt prime side up to F_5^2 = 25 plus the archimedean Gamma
factor logarithmic-derivative density; no zero-location data is read.

The proof reuses the `IntervalMatrixPSD.psd_2x2` and `psd_1x1` criteria.
The off-diagonal corner entry is negative, so the PSD statement is a genuine
cancellation certificate obtained by symmetric diagonalization.
-/

namespace BEDC.Derived.RHRoute.FibonacciWindowWeilMatrixPositivity

open BEDC.Algebra.Rel (RelCommRing)
open BEDC.Algebra.FiniteFold
open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumKernel
open BEDC.Real.RatNumLogEnclosure
open BEDC.Derived.RHRoute.IntervalMatrixPSD


abbrev Rat : Type :=
  RatNum

def natRat : Nat -> Rat
  | 0 => ratZero
  | 1 => ratOne
  | 2 => ratAdd ratOne ratOne
  | Nat.succ n => BEDC.Real.RatNumKernel.ratNat (Nat.succ n)

theorem ratMul_zero_right_local (x : Rat) :
    RatEq (ratMul x ratZero) ratZero := by
  unfold RatEq ratMul ratZero intToRat
  change
    IntEq (IntMul (IntMul x.num intZero) (ratDenInt ratZero))
      (IntMul intZero (ratDenInt (ratMul x ratZero)))
  exact IntEq_trans (intMul_right_congr (intMul_zero_right x.num))
    (IntEq_symm (intMul_zero_left (ratDenInt (ratMul x ratZero))))

theorem ratMul_zero_left_local (x : Rat) :
    RatEq (ratMul ratZero x) ratZero :=
  RatEq_trans _ _ _ (ratMul_comm ratZero x) (ratMul_zero_right_local x)

private def ratRing : RelCommRing Rat RatEq where
  zero := ratZero
  one := ratOne
  add := ratAdd
  mul := ratMul
  neg := ratNeg
  refl := RatEq_refl
  symm := RatEq_symm
  trans := by
    intro _ _ _
    exact RatEq_trans _ _ _
  add_congr := by
    intro _ _ _ _ hleft hright
    exact ratAdd_respects hleft hright
  mul_congr := by
    intro _ _ _ _ hleft hright
    exact ratMul_respects hleft hright
  neg_congr := by
    intro _ _ h
    exact ratNeg_respects h
  add_assoc := BEDC.Derived.LocatedReal.ratAdd_assoc_local
  add_comm := ratAdd_comm
  add_zero := ratAdd_zero_right
  zero_add := ratZero_add_left
  add_neg := BEDC.Derived.LocatedReal.ratAdd_neg_local
  neg_add := BEDC.Derived.LocatedReal.ratNeg_add_local
  mul_assoc := ratMul_assoc
  mul_one := ratMul_one_right
  one_mul := ratOne_mul_left
  mul_zero := ratMul_zero_right_local
  zero_mul := ratMul_zero_left_local
  left_distrib := BEDC.Real.RatNumKernel.ratMul_add_left
  right_distrib := BEDC.Real.RatNumKernel.ratMul_add_right
  mul_comm := ratMul_comm

private inductive RExpr where
  | var : Nat -> RExpr
  | zero : RExpr
  | one : RExpr
  | add : RExpr -> RExpr -> RExpr
  | mul : RExpr -> RExpr -> RExpr
  | neg : RExpr -> RExpr

private structure RTerm where
  neg : Bool
  vars : List Nat

private def rExprEval (vars : Nat -> Rat) : RExpr -> Rat
  | RExpr.var i => vars i
  | RExpr.zero => ratZero
  | RExpr.one => ratOne
  | RExpr.add a b => ratAdd (rExprEval vars a) (rExprEval vars b)
  | RExpr.mul a b => ratMul (rExprEval vars a) (rExprEval vars b)
  | RExpr.neg a => ratNeg (rExprEval vars a)

private def rMonoEval (vars : Nat -> Rat) : List Nat -> Rat
  | [] => ratOne
  | i :: is => ratMul (vars i) (rMonoEval vars is)

private def rTermEval (vars : Nat -> Rat) (t : RTerm) : Rat :=
  match t.neg with
  | false => rMonoEval vars t.vars
  | true => ratNeg (rMonoEval vars t.vars)

private def natEqBool : Nat -> Nat -> Bool
  | 0, 0 => true
  | 0, Nat.succ _ => false
  | Nat.succ _, 0 => false
  | Nat.succ a, Nat.succ b => natEqBool a b

private def natListEqBool : List Nat -> List Nat -> Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | x :: xs, y :: ys => if natEqBool x y then natListEqBool xs ys else false

private def natLeBool : Nat -> Nat -> Bool
  | 0, _ => true
  | Nat.succ _, 0 => false
  | Nat.succ a, Nat.succ b => natLeBool a b

private def natInsert (x : Nat) : List Nat -> List Nat
  | [] => [x]
  | y :: ys => if natLeBool x y then x :: y :: ys else y :: natInsert x ys

private def natSort : List Nat -> List Nat
  | [] => []
  | x :: xs => natInsert x (natSort xs)

private def rTermCanonical (t : RTerm) : RTerm :=
  { neg := t.neg, vars := natSort t.vars }

private def rTermNeg (t : RTerm) : RTerm :=
  { neg := !t.neg, vars := t.vars }

private def rTermMul (a b : RTerm) : RTerm :=
  { neg := (a.neg != b.neg), vars := a.vars ++ b.vars }

private def rTermsMulOne (t : RTerm) : List RTerm -> List RTerm
  | [] => []
  | u :: us => rTermMul t u :: rTermsMulOne t us

private def rTermsMul : List RTerm -> List RTerm -> List RTerm
  | [], _ => []
  | t :: ts, us => rTermsMulOne t us ++ rTermsMul ts us

private def rExprTerms : RExpr -> List RTerm
  | RExpr.var i => [{ neg := false, vars := [i] }]
  | RExpr.zero => []
  | RExpr.one => [{ neg := false, vars := [] }]
  | RExpr.add a b => rExprTerms a ++ rExprTerms b
  | RExpr.mul a b => rTermsMul (rExprTerms a) (rExprTerms b)
  | RExpr.neg a => List.map rTermNeg (rExprTerms a)

private def natLexLeBool : List Nat -> List Nat -> Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
      if natEqBool a b then natLexLeBool as bs else natLeBool a b

private def rTermLeBool (a b : RTerm) : Bool :=
  if natListEqBool a.vars b.vars then
    match a.neg, b.neg with
    | false, false => true
    | false, true => true
    | true, false => false
    | true, true => true
  else
    natLexLeBool a.vars b.vars

private def rTermInsert (t : RTerm) : List RTerm -> List RTerm
  | [] => [t]
  | u :: us =>
      if rTermLeBool t u then t :: u :: us else u :: rTermInsert t us

private def rTermSort : List RTerm -> List RTerm
  | [] => []
  | t :: ts => rTermInsert t (rTermSort ts)

private def rTermOppositeSame (a b : RTerm) : Bool :=
  match a.neg, b.neg with
  | false, false => false
  | false, true => natListEqBool a.vars b.vars
  | true, false => natListEqBool a.vars b.vars
  | true, true => false

private def rCancelStep : List RTerm -> RTerm -> List RTerm
  | [], t => [t]
  | u :: us, t =>
      if rTermOppositeSame t u then us else t :: u :: us

private def rCancelGo : List RTerm -> List RTerm -> List RTerm
  | acc, [] => acc
  | acc, t :: ts => rCancelGo (rCancelStep acc t) ts

private def rCancelTerms (terms : List RTerm) : List RTerm :=
  rTermSort (rCancelGo [] terms)

private def rExprNorm (e : RExpr) : List RTerm :=
  rCancelTerms (rTermSort (List.map rTermCanonical (rExprTerms e)))

private def rSumTerms (vars : Nat -> Rat) : List RTerm -> Rat
  | [] => ratZero
  | t :: terms => ratAdd (rTermEval vars t) (rSumTerms vars terms)

private theorem natInsert_perm (x : Nat) :
    ∀ xs : List Nat,
      ListPerm (natInsert x xs) (x :: xs)
  | [] => by
      exact ListPerm.cons x ListPerm.nil
  | y :: ys => by
      cases h : natLeBool x y
      · unfold natInsert
        rw [h]
        exact ListPerm.trans
          (ListPerm.cons y (natInsert_perm x ys))
          (ListPerm.swap y x ys)
      · unfold natInsert
        rw [h]
        exact listPerm_refl (x :: y :: ys)

private theorem natSort_perm :
    ∀ xs : List Nat, ListPerm (natSort xs) xs
  | [] => ListPerm.nil
  | x :: xs =>
      ListPerm.trans
        (natInsert_perm x (natSort xs))
        (ListPerm.cons x (natSort_perm xs))

private theorem rMonoEval_perm (vars : Nat -> Rat) :
    ∀ {xs ys : List Nat},
      ListPerm xs ys -> RatEq (rMonoEval vars xs) (rMonoEval vars ys)
  | _, _, ListPerm.nil =>
      RatEq_refl ratOne
  | _, _, ListPerm.cons x p => by
      exact ratMul_respects (RatEq_refl (vars x)) (rMonoEval_perm vars p)
  | _, _, ListPerm.swap x y xs => by
      exact RatEq_trans _ _ _
        (RatEq_symm (ratMul_assoc (vars x) (vars y) (rMonoEval vars xs)))
        (RatEq_trans _ _ _
          (ratMul_respects (ratMul_comm (vars x) (vars y))
            (RatEq_refl (rMonoEval vars xs)))
          (ratMul_assoc (vars y) (vars x) (rMonoEval vars xs)))
  | _, _, ListPerm.trans p q =>
      RatEq_trans _ _ _ (rMonoEval_perm vars p) (rMonoEval_perm vars q)

private theorem rTermCanonical_eval (vars : Nat -> Rat) (t : RTerm) :
    RatEq (rTermEval vars (rTermCanonical t)) (rTermEval vars t) := by
  cases t with
  | mk isNeg mono =>
      cases isNeg
      · exact rMonoEval_perm vars (natSort_perm mono)
      · exact ratNeg_respects (rMonoEval_perm vars (natSort_perm mono))

private theorem rSum_canonical (vars : Nat -> Rat) :
    ∀ terms : List RTerm,
      RatEq (rSumTerms vars (List.map rTermCanonical terms))
        (rSumTerms vars terms)
  | [] => RatEq_refl ratZero
  | t :: ts =>
      ratAdd_respects (rTermCanonical_eval vars t) (rSum_canonical vars ts)

private theorem rTermInsert_perm (t : RTerm) :
    ∀ terms : List RTerm,
      ListPerm (rTermInsert t terms) (t :: terms)
  | [] => by
      exact ListPerm.cons t ListPerm.nil
  | u :: us => by
      cases h : rTermLeBool t u
      · unfold rTermInsert
        rw [h]
        exact ListPerm.trans
          (ListPerm.cons u (rTermInsert_perm t us))
          (ListPerm.swap u t us)
      · unfold rTermInsert
        rw [h]
        exact listPerm_refl (t :: u :: us)

private theorem rTermSort_perm :
    ∀ terms : List RTerm,
      ListPerm (rTermSort terms) terms
  | [] => ListPerm.nil
  | t :: ts =>
      ListPerm.trans
        (rTermInsert_perm t (rTermSort ts))
        (ListPerm.cons t (rTermSort_perm ts))

private theorem rSum_perm (vars : Nat -> Rat) :
    ∀ {xs ys : List RTerm},
      ListPerm xs ys -> RatEq (rSumTerms vars xs) (rSumTerms vars ys)
  | _, _, ListPerm.nil =>
      RatEq_refl ratZero
  | _, _, ListPerm.cons x p => by
      exact ratAdd_respects (RatEq_refl (rTermEval vars x)) (rSum_perm vars p)
  | _, _, ListPerm.swap x y xs => by
      exact RatEq_trans _ _ _
        (RatEq_symm
          (BEDC.Derived.LocatedReal.ratAdd_assoc_local
            (rTermEval vars x) (rTermEval vars y) (rSumTerms vars xs)))
        (RatEq_trans _ _ _
          (ratAdd_respects
            (ratAdd_comm (rTermEval vars x) (rTermEval vars y))
            (RatEq_refl (rSumTerms vars xs)))
          (BEDC.Derived.LocatedReal.ratAdd_assoc_local
            (rTermEval vars y) (rTermEval vars x) (rSumTerms vars xs)))
  | _, _, ListPerm.trans p q =>
      RatEq_trans _ _ _ (rSum_perm vars p) (rSum_perm vars q)

private theorem rSum_sort (vars : Nat -> Rat) (terms : List RTerm) :
    RatEq (rSumTerms vars (rTermSort terms)) (rSumTerms vars terms) :=
  rSum_perm vars (rTermSort_perm terms)

private theorem natEqBool_eq_true :
    ∀ a b : Nat, natEqBool a b = true -> a = b
  | 0, 0, _ => rfl
  | 0, Nat.succ _, h => by cases h
  | Nat.succ _, 0, h => by cases h
  | Nat.succ a, Nat.succ b, h => by
      exact congrArg Nat.succ (natEqBool_eq_true a b h)

private theorem natListEqBool_eq_true :
    ∀ xs ys : List Nat, natListEqBool xs ys = true -> xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | x :: xs, y :: ys, h => by
      unfold natListEqBool at h
      cases heq : natEqBool x y
      · rw [heq] at h
        cases h
      · rw [heq] at h
        have headEq : x = y := natEqBool_eq_true x y heq
        have tailEq : xs = ys := natListEqBool_eq_true xs ys h
        cases headEq
        cases tailEq
        rfl

private theorem rTermOppositeSame_eval_zero
    (vars : Nat -> Rat) (t u : RTerm) :
    rTermOppositeSame t u = true ->
      RatEq (ratAdd (rTermEval vars t) (rTermEval vars u)) ratZero := by
  intro h
  cases t with
  | mk tNeg tVars =>
      cases u with
      | mk uNeg uVars =>
          cases tNeg <;> cases uNeg
          · cases h
          · unfold rTermOppositeSame at h
            have sameVars := natListEqBool_eq_true tVars uVars h
            rw [sameVars]
            change RatEq
              (ratAdd (rMonoEval vars uVars) (ratNeg (rMonoEval vars uVars)))
              ratZero
            exact BEDC.Derived.LocatedReal.ratAdd_neg_local (rMonoEval vars uVars)
          · unfold rTermOppositeSame at h
            have sameVars := natListEqBool_eq_true tVars uVars h
            rw [sameVars]
            change RatEq
              (ratAdd (ratNeg (rMonoEval vars uVars)) (rMonoEval vars uVars))
              ratZero
            exact BEDC.Derived.LocatedReal.ratNeg_add_local (rMonoEval vars uVars)
          · cases h

private theorem rCancelStep_sound (vars : Nat -> Rat) :
    ∀ acc : List RTerm, ∀ t : RTerm,
      RatEq (rSumTerms vars (rCancelStep acc t))
        (ratAdd (rTermEval vars t) (rSumTerms vars acc))
  | [], t => by
      exact RatEq_refl (ratAdd (rTermEval vars t) ratZero)
  | u :: us, t => by
      cases h : rTermOppositeSame t u
      · change RatEq (rSumTerms vars
          (if rTermOppositeSame t u then us else t :: u :: us))
          (ratAdd (rTermEval vars t)
            (ratAdd (rTermEval vars u) (rSumTerms vars us)))
        rw [h]
        exact RatEq_refl
          (ratAdd (rTermEval vars t)
            (ratAdd (rTermEval vars u) (rSumTerms vars us)))
      · change RatEq (rSumTerms vars
          (if rTermOppositeSame t u then us else t :: u :: us))
          (ratAdd (rTermEval vars t)
            (ratAdd (rTermEval vars u) (rSumTerms vars us)))
        rw [h]
        exact RatEq_symm
          (RatEq_trans _ _ _
            (RatEq_symm
              (BEDC.Derived.LocatedReal.ratAdd_assoc_local
                (rTermEval vars t) (rTermEval vars u) (rSumTerms vars us)))
            (RatEq_trans _ _ _
              (ratAdd_respects (rTermOppositeSame_eval_zero vars t u h)
                (RatEq_refl (rSumTerms vars us)))
              (ratZero_add_left (rSumTerms vars us))))

private theorem rCancelGo_sound (vars : Nat -> Rat) :
    ∀ acc terms : List RTerm,
      RatEq (rSumTerms vars (rCancelGo acc terms))
        (ratAdd (rSumTerms vars terms) (rSumTerms vars acc))
  | acc, [] => by
      exact RatEq_symm (ratZero_add_left (rSumTerms vars acc))
  | acc, t :: ts => by
      have tail := rCancelGo_sound vars (rCancelStep acc t) ts
      exact RatEq_trans _ _ _ tail
        (RatEq_trans _ _ _
          (ratAdd_respects (RatEq_refl (rSumTerms vars ts))
            (rCancelStep_sound vars acc t))
          (RatEq_trans _ _ _
            (RatEq_symm
              (BEDC.Derived.LocatedReal.ratAdd_assoc_local
                (rSumTerms vars ts) (rTermEval vars t) (rSumTerms vars acc)))
            (ratAdd_respects
              (ratAdd_comm (rSumTerms vars ts) (rTermEval vars t))
              (RatEq_refl (rSumTerms vars acc)))))

private theorem rCancelTerms_sound (vars : Nat -> Rat) (terms : List RTerm) :
    RatEq (rSumTerms vars (rCancelTerms terms)) (rSumTerms vars terms) := by
  unfold rCancelTerms
  exact RatEq_trans _ _ _
    (rSum_sort vars (rCancelGo [] terms))
    (RatEq_trans _ _ _
      (rCancelGo_sound vars [] terms)
      (RatEq_trans _ _ _
        (ratAdd_respects (RatEq_refl (rSumTerms vars terms))
          (RatEq_refl ratZero))
        (ratAdd_zero_right (rSumTerms vars terms))))

private theorem rSum_append (vars : Nat -> Rat) (xs ys : List RTerm) :
    RatEq (rSumTerms vars (xs ++ ys))
      (ratAdd (rSumTerms vars xs) (rSumTerms vars ys)) := by
  induction xs with
  | nil =>
      exact RatEq_symm (ratZero_add_left (rSumTerms vars ys))
  | cons x xs ih =>
      exact RatEq_trans _ _ _
        (ratAdd_respects (RatEq_refl (rTermEval vars x)) ih)
        (RatEq_symm
          (BEDC.Derived.LocatedReal.ratAdd_assoc_local
            (rTermEval vars x) (rSumTerms vars xs) (rSumTerms vars ys)))

private theorem rMonoEval_append (vars : Nat -> Rat) :
    ∀ xs ys : List Nat,
      RatEq (rMonoEval vars (xs ++ ys))
        (ratMul (rMonoEval vars xs) (rMonoEval vars ys))
  | [], ys => by
      exact RatEq_symm (ratOne_mul_left (rMonoEval vars ys))
  | x :: xs, ys => by
      exact RatEq_trans _ _ _
        (ratMul_respects (RatEq_refl (vars x)) (rMonoEval_append vars xs ys))
        (RatEq_symm
          (ratMul_assoc (vars x) (rMonoEval vars xs) (rMonoEval vars ys)))

private theorem rTermEval_neg (vars : Nat -> Rat) (t : RTerm) :
    RatEq (rTermEval vars (rTermNeg t)) (ratNeg (rTermEval vars t)) := by
  cases t with
  | mk isNeg mono =>
      cases isNeg
      · exact RatEq_refl (ratNeg (rMonoEval vars mono))
      · exact RatEq_symm
          (BEDC.Derived.LocatedReal.ratNeg_neg_local (rMonoEval vars mono))

private theorem rTermEval_mul (vars : Nat -> Rat) (t u : RTerm) :
    RatEq (rTermEval vars (rTermMul t u))
      (ratMul (rTermEval vars t) (rTermEval vars u)) := by
  cases t with
  | mk tNeg tVars =>
      cases u with
      | mk uNeg uVars =>
          cases tNeg <;> cases uNeg
          · exact rMonoEval_append vars tVars uVars
          · exact RatEq_trans _ _ _
              (ratNeg_respects (rMonoEval_append vars tVars uVars))
              (RatEq_symm (ratRing.mul_neg (rMonoEval vars tVars)
                (rMonoEval vars uVars)))
          · exact RatEq_trans _ _ _
              (ratNeg_respects (rMonoEval_append vars tVars uVars))
              (RatEq_symm (ratRing.neg_mul (rMonoEval vars tVars)
                (rMonoEval vars uVars)))
          · exact RatEq_trans _ _ _
              (rMonoEval_append vars tVars uVars)
              (RatEq_symm (ratRing.neg_neg_mul_neg
                (rMonoEval vars tVars) (rMonoEval vars uVars)))

private theorem rSum_neg (vars : Nat -> Rat) :
    ∀ terms : List RTerm,
      RatEq (rSumTerms vars (List.map rTermNeg terms))
        (ratNeg (rSumTerms vars terms))
  | [] => by
      exact RatEq_symm ratRing.neg_zero
  | t :: ts => by
      exact RatEq_trans _ _ _
        (ratAdd_respects (rTermEval_neg vars t) (rSum_neg vars ts))
        (RatEq_symm
          (BEDC.Derived.LocatedReal.ratNeg_add_dist_local
            (rTermEval vars t) (rSumTerms vars ts)))

private theorem rTermsMulOne_sound (vars : Nat -> Rat) (t : RTerm) :
    ∀ terms : List RTerm,
      RatEq (rSumTerms vars (rTermsMulOne t terms))
        (ratMul (rTermEval vars t) (rSumTerms vars terms))
  | [] => by
      exact RatEq_symm (ratMul_zero_right_local (rTermEval vars t))
  | u :: us => by
      exact RatEq_trans _ _ _
        (ratAdd_respects (rTermEval_mul vars t u)
          (rTermsMulOne_sound vars t us))
        (RatEq_symm
          (BEDC.Real.RatNumKernel.ratMul_add_left
            (rTermEval vars t) (rTermEval vars u) (rSumTerms vars us)))

private theorem rTermsMul_sound (vars : Nat -> Rat) :
    ∀ xs ys : List RTerm,
      RatEq (rSumTerms vars (rTermsMul xs ys))
        (ratMul (rSumTerms vars xs) (rSumTerms vars ys))
  | [], ys => by
      exact RatEq_symm (ratMul_zero_left_local (rSumTerms vars ys))
  | x :: xs, ys => by
      exact RatEq_trans _ _ _
        (rSum_append vars (rTermsMulOne x ys) (rTermsMul xs ys))
        (RatEq_trans _ _ _
          (ratAdd_respects
            (rTermsMulOne_sound vars x ys)
            (rTermsMul_sound vars xs ys))
          (RatEq_symm
            (BEDC.Real.RatNumKernel.ratMul_add_right
              (rTermEval vars x) (rSumTerms vars xs) (rSumTerms vars ys))))

private theorem rExprTerms_sound :
    ∀ (vars : Nat -> Rat) (e : RExpr),
      RatEq (rExprEval vars e) (rSumTerms vars (rExprTerms e))
  | vars, RExpr.var i =>
      RatEq_trans _ _ _ (RatEq_symm (ratMul_one_right (vars i)))
        (RatEq_symm (ratAdd_zero_right (ratMul (vars i) ratOne)))
  | vars, RExpr.zero =>
      RatEq_refl ratZero
  | vars, RExpr.one =>
      RatEq_symm (ratAdd_zero_right ratOne)
  | vars, RExpr.add a b => by
      exact RatEq_trans _ _ _
        (ratAdd_respects (rExprTerms_sound vars a) (rExprTerms_sound vars b))
        (RatEq_symm (rSum_append vars (rExprTerms a) (rExprTerms b)))
  | vars, RExpr.mul a b => by
      exact RatEq_trans _ _ _
        (ratMul_respects (rExprTerms_sound vars a) (rExprTerms_sound vars b))
        (RatEq_symm (rTermsMul_sound vars (rExprTerms a) (rExprTerms b)))
  | vars, RExpr.neg a => by
      exact RatEq_trans _ _ _
        (ratNeg_respects (rExprTerms_sound vars a))
        (RatEq_symm (rSum_neg vars (rExprTerms a)))

private theorem rExprNorm_sound (vars : Nat -> Rat) (e : RExpr) :
    RatEq (rExprEval vars e) (rSumTerms vars (rExprNorm e)) := by
  exact RatEq_trans _ _ _
    (rExprTerms_sound vars e)
    (RatEq_trans _ _ _
      (RatEq_symm (rSum_canonical vars (rExprTerms e)))
      (RatEq_trans _ _ _
        (RatEq_symm
          (rSum_sort vars (List.map rTermCanonical (rExprTerms e))))
        (RatEq_symm
          (rCancelTerms_sound vars
            (rTermSort (List.map rTermCanonical (rExprTerms e)))))))

private theorem rExpr_same_norm (vars : Nat -> Rat) (a b : RExpr)
    (h : rExprNorm a = rExprNorm b) :
    RatEq (rExprEval vars a) (rExprEval vars b) := by
  have left := rExprNorm_sound vars a
  have right := rExprNorm_sound vars b
  rw [h] at left
  exact RatEq_trans _ _ _ left (RatEq_symm right)

private def rV (n : Nat) : RExpr :=
  RExpr.var n

private def rAdd (x y : RExpr) : RExpr :=
  RExpr.add x y

private def rMul (x y : RExpr) : RExpr :=
  RExpr.mul x y

private def rNeg (x : RExpr) : RExpr :=
  RExpr.neg x

private def rSub (x y : RExpr) : RExpr :=
  rAdd x (rNeg y)

private def rTwo : RExpr :=
  rAdd RExpr.one RExpr.one


private def twoRat : Rat :=
  natRat 2

private def aW : Rat :=
  natRat 303318

private def bW : Rat :=
  ratNeg (natRat 12152)

private def cW : Rat :=
  ratNeg (natRat 193136)

private def b11W : Rat :=
  natRat 110182

private def b12W : Rat :=
  ratNeg (natRat 24304)

private def b22W : Rat :=
  natRat 606636

private def acW : Rat :=
  natRat 496454

private def lambdaW : Rat :=
  natRat 100000

private def aShiftW : Rat :=
  natRat 203318

private def b11ShiftW : Rat :=
  natRat 10182

private def b22ShiftW : Rat :=
  natRat 406636

private def acShiftW : Rat :=
  natRat 396454

private def norm3W (x0 x1 x2 : Rat) : Rat :=
  ratAdd
    (ratAdd (ratMul x0 x0) (ratMul x1 x1))
    (ratMul x2 x2)

private def quadCoeff (a b c x0 x1 x2 : Rat) : Rat :=
  ratAdd
    (ratAdd
      (ratMul a (norm3W x0 x1 x2))
      (ratMul (ratMul twoRat b)
        (ratAdd (ratMul x0 x1) (ratMul x1 x2))))
    (ratMul (ratMul twoRat c) (ratMul x0 x2))

/-- The scaled rational Weil quadratic form on the three Fibonacci-hat basis elements. -/
def quadW (x0 x1 x2 : Rat) : Rat :=
  ratAdd
    (ratAdd
      (ratMul aW
        (ratAdd
          (ratAdd (ratMul x0 x0) (ratMul x1 x1))
          (ratMul x2 x2)))
    (ratMul (ratMul twoRat bW)
      (ratAdd (ratMul x0 x1) (ratMul x1 x2))))
    (ratMul (ratMul twoRat cW) (ratMul x0 x2))

def shiftedQuadW (x0 x1 x2 : Rat) : Rat :=
  quadCoeff aShiftW bW cW x0 x1 x2

private def block2W (x0 x1 x2 : Rat) : Rat :=
  ratAdd
    (ratAdd
      (ratMul b11W (ratMul (ratAdd x0 x2) (ratAdd x0 x2)))
      (ratMul (ratMul twoRat b12W) (ratMul (ratAdd x0 x2) x1)))
    (ratMul b22W (ratMul x1 x1))

private def block1W (x0 x2 : Rat) : Rat :=
  ratMul acW (ratMul (ratSub x0 x2) (ratSub x0 x2))

private def block2ShiftW (x0 x1 x2 : Rat) : Rat :=
  ratAdd
    (ratAdd
      (ratMul b11ShiftW (ratMul (ratAdd x0 x2) (ratAdd x0 x2)))
      (ratMul (ratMul twoRat b12W) (ratMul (ratAdd x0 x2) x1)))
    (ratMul b22ShiftW (ratMul x1 x1))

private def block1ShiftW (x0 x2 : Rat) : Rat :=
  ratMul acShiftW (ratMul (ratSub x0 x2) (ratSub x0 x2))

private def quadDiagLeftExpr : RExpr :=
  rMul rTwo
    (rAdd
      (rAdd
        (rMul (rV 0)
          (rAdd
            (rAdd (rMul (rV 3) (rV 3)) (rMul (rV 4) (rV 4)))
            (rMul (rV 5) (rV 5))))
        (rMul (rMul rTwo (rV 1))
          (rAdd (rMul (rV 3) (rV 4)) (rMul (rV 4) (rV 5)))))
      (rMul (rMul rTwo (rV 2)) (rMul (rV 3) (rV 5))))

private def quadDiagRightExpr : RExpr :=
  rAdd
    (rAdd
      (rAdd
        (rMul (rAdd (rV 0) (rV 2))
          (rMul (rAdd (rV 3) (rV 5)) (rAdd (rV 3) (rV 5))))
        (rMul (rMul rTwo (rMul rTwo (rV 1)))
          (rMul (rAdd (rV 3) (rV 5)) (rV 4))))
      (rMul (rMul rTwo (rV 0)) (rMul (rV 4) (rV 4))))
    (rMul (rAdd (rV 0) (rNeg (rV 2)))
      (rMul (rSub (rV 3) (rV 5)) (rSub (rV 3) (rV 5))))

private theorem quadDiag_expr_norm :
    rExprNorm quadDiagLeftExpr = rExprNorm quadDiagRightExpr :=
  rfl

private def quadCoeffExpr (a b c x0 x1 x2 : RExpr) : RExpr :=
  rAdd
    (rAdd
      (rMul a
        (rAdd
          (rAdd (rMul x0 x0) (rMul x1 x1))
          (rMul x2 x2)))
      (rMul (rMul rTwo b)
        (rAdd (rMul x0 x1) (rMul x1 x2))))
    (rMul (rMul rTwo c) (rMul x0 x2))

private def norm3Expr (x0 x1 x2 : RExpr) : RExpr :=
  rAdd
    (rAdd (rMul x0 x0) (rMul x1 x1))
    (rMul x2 x2)

private def quadSplitLeftExpr : RExpr :=
  quadCoeffExpr (rAdd (rV 0) (rV 1)) (rV 2) (rV 3) (rV 4) (rV 5) (rV 6)

private def quadSplitRightExpr : RExpr :=
  rAdd
    (rMul (rV 0) (norm3Expr (rV 4) (rV 5) (rV 6)))
    (quadCoeffExpr (rV 1) (rV 2) (rV 3) (rV 4) (rV 5) (rV 6))

private theorem quadSplit_expr_norm :
    rExprNorm quadSplitLeftExpr = rExprNorm quadSplitRightExpr :=
  rfl

private theorem quadW_diagonalization_param
    (a b c x0 x1 x2 : Rat) :
    RatEq
      (ratMul twoRat
        (ratAdd
          (ratAdd
            (ratMul a
              (ratAdd
                (ratAdd (ratMul x0 x0) (ratMul x1 x1))
                (ratMul x2 x2)))
            (ratMul (ratMul twoRat b)
              (ratAdd (ratMul x0 x1) (ratMul x1 x2))))
          (ratMul (ratMul twoRat c) (ratMul x0 x2))))
      (ratAdd
        (ratAdd
          (ratAdd
            (ratMul (ratAdd a c)
              (ratMul (ratAdd x0 x2) (ratAdd x0 x2)))
            (ratMul (ratMul twoRat (ratMul twoRat b))
              (ratMul (ratAdd x0 x2) x1)))
          (ratMul (ratMul twoRat a) (ratMul x1 x1)))
        (ratMul (ratAdd a (ratNeg c))
          (ratMul (ratSub x0 x2) (ratSub x0 x2)))) := by
  let vars : Nat -> Rat := fun
    | 0 => a
    | 1 => b
    | 2 => c
    | 3 => x0
    | 4 => x1
    | _ => x2
  have base :
      RatEq (rExprEval vars quadDiagLeftExpr)
        (rExprEval vars quadDiagRightExpr) :=
    rExpr_same_norm vars quadDiagLeftExpr quadDiagRightExpr quadDiag_expr_norm
  change
    RatEq
      (ratMul twoRat
        (ratAdd
          (ratAdd
            (ratMul a
              (ratAdd
                (ratAdd (ratMul x0 x0) (ratMul x1 x1))
                (ratMul x2 x2)))
            (ratMul (ratMul twoRat b)
              (ratAdd (ratMul x0 x1) (ratMul x1 x2))))
          (ratMul (ratMul twoRat c) (ratMul x0 x2))))
      (ratAdd
        (ratAdd
          (ratAdd
            (ratMul (ratAdd a c)
              (ratMul (ratAdd x0 x2) (ratAdd x0 x2)))
            (ratMul (ratMul twoRat (ratMul twoRat b))
              (ratMul (ratAdd x0 x2) x1)))
          (ratMul (ratMul twoRat a) (ratMul x1 x1)))
        (ratMul (ratAdd a (ratNeg c))
          (ratMul (ratAdd x0 (ratNeg x2)) (ratAdd x0 (ratNeg x2))))) at base
  exact base

private theorem quadCoeff_split_param
    (lambda a b c x0 x1 x2 : Rat) :
    RatEq
      (quadCoeff (ratAdd lambda a) b c x0 x1 x2)
      (ratAdd
        (ratMul lambda (norm3W x0 x1 x2))
        (quadCoeff a b c x0 x1 x2)) := by
  let vars : Nat -> Rat := fun
    | 0 => lambda
    | 1 => a
    | 2 => b
    | 3 => c
    | 4 => x0
    | 5 => x1
    | _ => x2
  have base :
      RatEq (rExprEval vars quadSplitLeftExpr)
        (rExprEval vars quadSplitRightExpr) :=
    rExpr_same_norm vars quadSplitLeftExpr quadSplitRightExpr quadSplit_expr_norm
  change
    RatEq
      (quadCoeff (ratAdd lambda a) b c x0 x1 x2)
      (ratAdd
        (ratMul lambda (norm3W x0 x1 x2))
        (quadCoeff a b c x0 x1 x2)) at base
  exact base

private theorem quadCoeff_respects
    {a a' b b' c c' x0 x1 x2 : Rat}
    (ha : RatEq a a') (hb : RatEq b b') (hc : RatEq c c') :
    RatEq (quadCoeff a b c x0 x1 x2) (quadCoeff a' b' c' x0 x1 x2) := by
  unfold quadCoeff
  exact ratAdd_respects
    (ratAdd_respects
      (ratMul_respects ha (RatEq_refl (norm3W x0 x1 x2)))
      (ratMul_respects
        (ratMul_respects (RatEq_refl twoRat) hb)
        (RatEq_refl (ratAdd (ratMul x0 x1) (ratMul x1 x2)))))
    (ratMul_respects
      (ratMul_respects (RatEq_refl twoRat) hc)
      (RatEq_refl (ratMul x0 x2)))

private theorem natRat_as_ratNat (n : Nat) :
    RatEq (natRat n) (ratNat n) := by
  cases n with
  | zero =>
      unfold natRat ratNat ratZero intToRat intZero intOfNat
      exact RatEq_refl _
  | succ n =>
      cases n with
      | zero =>
          unfold natRat
          unfold ratNat ratOne intToRat intOne intOfNat
          exact RatEq_refl _
      | succ n =>
          cases n with
          | zero =>
              have oneKernel : RatEq ratOne (ratNat 1) := by
                unfold ratNat ratOne intToRat intOne intOfNat
                exact RatEq_refl _
              change RatEq (ratAdd ratOne ratOne) (ratNat 2)
              exact RatEq_trans _ _ _
                (ratAdd_respects oneKernel oneKernel)
                (ratNat_add 1 1)
          | succ n =>
              change
                RatEq
                  (natRat (Nat.succ (Nat.succ (Nat.succ n))))
                  (ratNat (Nat.succ (Nat.succ (Nat.succ n))))
              exact RatEq_refl _

private theorem natRat_large_mul (m n : Nat) :
    RatEq (ratMul (natRat m) (natRat n)) (natRat (m * n)) :=
  RatEq_trans _ _ _
    (ratMul_respects (natRat_as_ratNat m) (natRat_as_ratNat n))
    (RatEq_trans _ _ _ (ratNat_mul m n) (RatEq_symm (natRat_as_ratNat (m * n))))

private theorem natRat_large_nonneg (n : Nat) :
    ratLe ratZero (natRat n) :=
  ratLe_of_RatEq_right (ratNat_nonneg n) (RatEq_symm (natRat_as_ratNat n))

private theorem ratLe_congr {x x' y y' : Rat}
    (hx : RatEq x x') (hy : RatEq y y') (h : ratLe x' y') : ratLe x y :=
  ratLe_of_RatEq_right (ratLe_of_RatEq_left hx h) (RatEq_symm hy)

private theorem ratAdd_nonneg {x y : Rat}
    (hx : ratLe ratZero x) (hy : ratLe ratZero y) :
    ratLe ratZero (ratAdd x y) := by
  have raw : ratLe (ratAdd ratZero ratZero) (ratAdd x y) :=
    ratAdd_le_add hx hy
  exact ratLe_of_RatEq_left (ratZero_add_left ratZero) raw

private theorem natRat_two_eq_ratTwo :
    RatEq twoRat ratTwo := by
  have oneKernel : RatEq ratOne (ratNat 1) := by
    unfold ratNat ratOne intToRat intOne intOfNat
    exact RatEq_refl _
  have toNatTwo : RatEq twoRat (ratNat 2) := by
    change RatEq (ratAdd ratOne ratOne) (ratNat 2)
    exact RatEq_trans _ _ _
      (ratAdd_respects oneKernel oneKernel)
      (ratNat_add 1 1)
  have ratNatTwo : RatEq (ratNat 2) ratTwo := by
    change RatEq (ratNat 2) ratTwo
    exact RatEq_refl _
  exact RatEq_trans _ _ _ toNatTwo ratNatTwo

private theorem natRat_two_pos :
    ratLt ratZero twoRat :=
  ratLt_of_RatEq_right ratTwo_pos (RatEq_symm natRat_two_eq_ratTwo)

private theorem ratLe_of_mul_pos_left {a x : Rat} :
    ratLt ratZero a -> ratLe ratZero (ratMul a x) -> ratLe ratZero x := by
  intro apos h
  have productRight : ratLe (ratMul ratZero a) (ratMul x a) :=
    ratLe_respects
      (RatEq_symm (ratMul_zero_left_local a))
      (ratMul_comm a x)
      h
  exact ratMul_le_cancel_right apos productRight

private theorem a_plus_c_eq_b11 :
    RatEq (ratAdd aW cW) b11W := by
  change RatEq (ratAdd (natRat 303318) (ratNeg (natRat 193136))) (natRat 110182)
  have subEq : RatEq (ratSub (ratNat 303318) (ratNat 193136)) (ratNat 110182) := by
    exact ratNat_sub_of_le (a := 303318) (b := 193136)
      (Nat.le.intro (n := 193136) (m := 303318) (k := 110182) (by rfl))
  change RatEq (ratSub (ratNat 303318) (ratNat 193136)) (ratNat 110182)
  exact subEq

private theorem two_b_eq_b12 :
    RatEq (ratMul twoRat bW) b12W := by
  change RatEq (ratMul twoRat (ratNeg (natRat 12152))) (ratNeg (natRat 24304))
  have left : RatEq (ratMul twoRat (ratNeg (natRat 12152)))
      (ratNeg (ratMul twoRat (natRat 12152))) :=
    ratRing.mul_neg twoRat (natRat 12152)
  have prod : RatEq (ratMul twoRat (natRat 12152)) (natRat 24304) := by
    have raw : RatEq (ratMul (natRat 2) (natRat 12152)) (natRat (2 * 12152)) :=
      natRat_large_mul 2 12152
    change RatEq (ratMul twoRat (natRat 12152)) (natRat 24304) at raw
    exact raw
  exact RatEq_trans _ _ _ left (ratNeg_respects prod)

private theorem two_a_eq_b22 :
    RatEq (ratMul twoRat aW) b22W := by
  change RatEq (ratMul (natRat 2) (natRat 303318)) (natRat 606636)
  have raw := natRat_large_mul 2 303318
  change RatEq (ratMul (natRat 2) (natRat 303318)) (natRat 606636) at raw
  exact raw

private theorem a_sub_c_eq_ac :
    RatEq (ratAdd aW (ratNeg cW)) acW := by
  change RatEq (ratAdd (natRat 303318) (ratNeg (ratNeg (natRat 193136)))) (natRat 496454)
  exact RatEq_trans _ _ _
    (ratAdd_respects (RatEq_refl (natRat 303318))
      (BEDC.Derived.LocatedReal.ratNeg_neg_local (natRat 193136)))
    (by
      have raw := ratNat_add 303318 193136
      change RatEq (ratAdd (natRat 303318) (natRat 193136)) (natRat 496454) at raw
      exact raw)

private theorem lambda_plus_aShift_eq_a :
    RatEq (ratAdd lambdaW aShiftW) aW := by
  unfold lambdaW aShiftW aW
  have raw := ratNat_add 100000 203318
  change RatEq (ratAdd (natRat 100000) (natRat 203318)) (natRat 303318) at raw
  exact raw

private theorem aShift_plus_c_eq_b11Shift :
    RatEq (ratAdd aShiftW cW) b11ShiftW := by
  change RatEq (ratAdd (natRat 203318) (ratNeg (natRat 193136))) (natRat 10182)
  have subEq : RatEq (ratSub (ratNat 203318) (ratNat 193136)) (ratNat 10182) := by
    exact ratNat_sub_of_le (a := 203318) (b := 193136)
      (Nat.le.intro (n := 193136) (m := 203318) (k := 10182) (by rfl))
  change RatEq (ratSub (ratNat 203318) (ratNat 193136)) (ratNat 10182)
  exact subEq

private theorem two_aShift_eq_b22Shift :
    RatEq (ratMul twoRat aShiftW) b22ShiftW := by
  change RatEq (ratMul (natRat 2) (natRat 203318)) (natRat 406636)
  have raw := natRat_large_mul 2 203318
  change RatEq (ratMul (natRat 2) (natRat 203318)) (natRat 406636) at raw
  exact raw

private theorem aShift_sub_c_eq_acShift :
    RatEq (ratAdd aShiftW (ratNeg cW)) acShiftW := by
  change RatEq (ratAdd (natRat 203318) (ratNeg (ratNeg (natRat 193136)))) (natRat 396454)
  exact RatEq_trans _ _ _
    (ratAdd_respects (RatEq_refl (natRat 203318))
      (BEDC.Derived.LocatedReal.ratNeg_neg_local (natRat 193136)))
    (by
      have raw := ratNat_add 203318 193136
      change RatEq (ratAdd (natRat 203318) (natRat 193136)) (natRat 396454) at raw
      exact raw)

private theorem quadW_split_shifted (x0 x1 x2 : Rat) :
    RatEq (quadW x0 x1 x2)
      (ratAdd
        (ratMul lambdaW (norm3W x0 x1 x2))
        (shiftedQuadW x0 x1 x2)) := by
  unfold quadW shiftedQuadW aW bW cW lambdaW aShiftW
  have split := quadCoeff_split_param
    (natRat 100000) (natRat 203318)
    (ratNeg (natRat 12152)) (ratNeg (natRat 193136)) x0 x1 x2
  exact RatEq_trans _ _ _
    (quadCoeff_respects
      (RatEq_symm lambda_plus_aShift_eq_a)
      (RatEq_refl (ratNeg (natRat 12152)))
      (RatEq_refl (ratNeg (natRat 193136))))
    split

/-- Symmetric diagonalization of the concrete Weil matrix. -/
theorem quadW_diagonalization (x0 x1 x2 : Rat) :
    RatEq (ratMul twoRat (quadW x0 x1 x2))
      (ratAdd (block2W x0 x1 x2) (block1W x0 x2)) := by
  unfold quadW block2W block1W aW bW cW b11W b12W b22W acW
  have base := quadW_diagonalization_param
    (natRat 303318) (ratNeg (natRat 12152)) (ratNeg (natRat 193136)) x0 x1 x2
  exact RatEq_trans _ _ _ base
    (ratAdd_respects
      (ratAdd_respects
        (ratAdd_respects
          (ratMul_respects a_plus_c_eq_b11
            (RatEq_refl (ratMul (ratAdd x0 x2) (ratAdd x0 x2))))
          (ratMul_respects
            (ratMul_respects (RatEq_refl twoRat) two_b_eq_b12)
            (RatEq_refl (ratMul (ratAdd x0 x2) x1))))
        (ratMul_respects two_a_eq_b22 (RatEq_refl (ratMul x1 x1))))
      (ratMul_respects a_sub_c_eq_ac
        (RatEq_refl (ratMul (ratSub x0 x2) (ratSub x0 x2)))))

theorem shiftedQuadW_diagonalization (x0 x1 x2 : Rat) :
    RatEq (ratMul twoRat (shiftedQuadW x0 x1 x2))
      (ratAdd (block2ShiftW x0 x1 x2) (block1ShiftW x0 x2)) := by
  unfold shiftedQuadW block2ShiftW block1ShiftW aShiftW bW cW b11ShiftW b12W
    b22ShiftW acShiftW
  have base := quadW_diagonalization_param
    (natRat 203318) (ratNeg (natRat 12152)) (ratNeg (natRat 193136)) x0 x1 x2
  exact RatEq_trans _ _ _ base
    (ratAdd_respects
      (ratAdd_respects
        (ratAdd_respects
          (ratMul_respects aShift_plus_c_eq_b11Shift
            (RatEq_refl (ratMul (ratAdd x0 x2) (ratAdd x0 x2))))
          (ratMul_respects
            (ratMul_respects (RatEq_refl twoRat) two_b_eq_b12)
            (RatEq_refl (ratMul (ratAdd x0 x2) x1))))
        (ratMul_respects two_aShift_eq_b22Shift (RatEq_refl (ratMul x1 x1))))
      (ratMul_respects aShift_sub_c_eq_acShift
        (RatEq_refl (ratMul (ratSub x0 x2) (ratSub x0 x2)))))

theorem b11_nonneg : ratLe ratZero b11W := by
  unfold b11W
  exact natRat_large_nonneg 110182

theorem b22_nonneg : ratLe ratZero b22W := by
  unfold b22W
  exact natRat_large_nonneg 606636

theorem ac_nonneg : ratLe ratZero acW := by
  unfold acW
  exact natRat_large_nonneg 496454

theorem b11Shift_nonneg : ratLe ratZero b11ShiftW := by
  unfold b11ShiftW
  exact natRat_large_nonneg 10182

theorem b22Shift_nonneg : ratLe ratZero b22ShiftW := by
  unfold b22ShiftW
  exact natRat_large_nonneg 406636

theorem acShift_nonneg : ratLe ratZero acShiftW := by
  unfold acShiftW
  exact natRat_large_nonneg 396454

theorem det_cond : ratLe (ratMul b12W b12W) (ratMul b11W b22W) := by
  unfold b12W b11W b22W
  have leftEq : RatEq (ratMul (ratNeg (natRat 24304)) (ratNeg (natRat 24304)))
      (natRat 590684416) := by
    exact RatEq_trans _ _ _
      (ratRing.neg_neg_mul_neg (natRat 24304) (natRat 24304))
      (by
        have raw := natRat_large_mul 24304 24304
        change RatEq (ratMul (natRat 24304) (natRat 24304)) (natRat 590684416) at raw
        exact raw)
  have rightEq : RatEq (ratMul (natRat 110182) (natRat 606636))
      (natRat 66840367752) := by
    have raw := natRat_large_mul 110182 606636
    change RatEq (ratMul (natRat 110182) (natRat 606636)) (natRat 66840367752) at raw
    exact raw
  exact ratLe_congr leftEq rightEq
    (by
      change ratLe (ratNat 590684416) (ratNat 66840367752)
      exact ratNat_le_of_nat_le
        (Nat.le.intro (n := 590684416) (m := 66840367752) (k := 66249683336) (by rfl)))

theorem detShift_cond : ratLe (ratMul b12W b12W) (ratMul b11ShiftW b22ShiftW) := by
  unfold b12W b11ShiftW b22ShiftW
  have leftEq : RatEq (ratMul (ratNeg (natRat 24304)) (ratNeg (natRat 24304)))
      (natRat 590684416) := by
    exact RatEq_trans _ _ _
      (ratRing.neg_neg_mul_neg (natRat 24304) (natRat 24304))
      (by
        have raw := natRat_large_mul 24304 24304
        change RatEq (ratMul (natRat 24304) (natRat 24304)) (natRat 590684416) at raw
        exact raw)
  have rightEq : RatEq (ratMul (natRat 10182) (natRat 406636))
      (natRat 4140367752) := by
    have raw := natRat_large_mul 10182 406636
    change RatEq (ratMul (natRat 10182) (natRat 406636)) (natRat 4140367752) at raw
    exact raw
  exact ratLe_congr leftEq rightEq
    (by
      change ratLe (ratNat 590684416) (ratNat 4140367752)
      exact ratNat_le_of_nat_le
        (Nat.le.intro (n := 590684416) (m := 4140367752) (k := 3549683336) (by rfl)))

theorem two_quadW_nonneg (x0 x1 x2 : Rat) :
    ratLe ratZero (ratMul twoRat (quadW x0 x1 x2)) := by
  have block2Nonneg : ratLe ratZero (block2W x0 x1 x2) := by
    unfold block2W b11W b12W b22W twoRat
    exact psd_2x2 (natRat 110182) (ratNeg (natRat 24304)) (natRat 606636)
      b11_nonneg b22_nonneg det_cond (ratAdd x0 x2) x1
  have block1Nonneg : ratLe ratZero (block1W x0 x2) := by
    unfold block1W acW
    exact psd_1x1 (natRat 496454) (ratSub x0 x2) ac_nonneg
  exact ratLe_of_RatEq_right
    (ratAdd_nonneg block2Nonneg block1Nonneg)
    (RatEq_symm (quadW_diagonalization x0 x1 x2))

/-- The concrete degree-3 Fibonacci-window Weil matrix is PSD over exact rationals. -/
theorem weil_window3_matrix_psd (x0 x1 x2 : Rat) :
    ratLe ratZero (quadW x0 x1 x2) :=
  ratLe_of_mul_pos_left natRat_two_pos (two_quadW_nonneg x0 x1 x2)

theorem two_shiftedQuadW_nonneg (x0 x1 x2 : Rat) :
    ratLe ratZero (ratMul twoRat (shiftedQuadW x0 x1 x2)) := by
  have block2Nonneg : ratLe ratZero (block2ShiftW x0 x1 x2) := by
    unfold block2ShiftW b11ShiftW b12W b22ShiftW twoRat
    exact psd_2x2 (natRat 10182) (ratNeg (natRat 24304)) (natRat 406636)
      b11Shift_nonneg b22Shift_nonneg detShift_cond (ratAdd x0 x2) x1
  have block1Nonneg : ratLe ratZero (block1ShiftW x0 x2) := by
    unfold block1ShiftW acShiftW
    exact psd_1x1 (natRat 396454) (ratSub x0 x2) acShift_nonneg
  exact ratLe_of_RatEq_right
    (ratAdd_nonneg block2Nonneg block1Nonneg)
    (RatEq_symm (shiftedQuadW_diagonalization x0 x1 x2))

theorem shiftedQuadW_nonneg (x0 x1 x2 : Rat) :
    ratLe ratZero (shiftedQuadW x0 x1 x2) :=
  ratLe_of_mul_pos_left natRat_two_pos (two_shiftedQuadW_nonneg x0 x1 x2)

theorem weil_window3_matrix_lower_bound (x0 x1 x2 : Rat) :
    ratLe
      (ratMul lambdaW (norm3W x0 x1 x2))
      (quadW x0 x1 x2) := by
  exact ratLe_of_RatEq_right
    (ratLe_add_nonneg_right
      (ratMul lambdaW (norm3W x0 x1 x2))
      (shiftedQuadW x0 x1 x2)
      (shiftedQuadW_nonneg x0 x1 x2))
    (RatEq_symm (quadW_split_shifted x0 x1 x2))

private def e0ExprLeft : RExpr :=
  rAdd
    (rAdd
      (rMul (rV 1)
        (rAdd
          (rAdd (rMul RExpr.one RExpr.one) (rMul RExpr.zero RExpr.zero))
          (rMul RExpr.zero RExpr.zero)))
      (rMul (rMul (rV 0) (rV 2))
        (rAdd (rMul RExpr.one RExpr.zero) (rMul RExpr.zero RExpr.zero))))
    (rMul (rMul (rV 0) (rV 3)) (rMul RExpr.one RExpr.zero))

private def e0ExprRight : RExpr :=
  rV 1

private theorem e0_expr_norm : rExprNorm e0ExprLeft = rExprNorm e0ExprRight :=
  rfl

theorem quadW_e0 :
    RatEq (quadW (natRat 1) ratZero ratZero) (natRat 303318) := by
  unfold quadW aW bW cW
  let vars : Nat -> Rat := fun
    | 0 => twoRat
    | 1 => natRat 303318
    | 2 => ratNeg (natRat 12152)
    | _ => ratNeg (natRat 193136)
  have base : RatEq (rExprEval vars e0ExprLeft) (rExprEval vars e0ExprRight) :=
    rExpr_same_norm vars e0ExprLeft e0ExprRight e0_expr_norm
  change
    RatEq
      (ratAdd
        (ratAdd
          (ratMul (natRat 303318)
            (ratAdd
              (ratAdd (ratMul (natRat 1) (natRat 1)) (ratMul ratZero ratZero))
              (ratMul ratZero ratZero)))
          (ratMul (ratMul twoRat (ratNeg (natRat 12152)))
            (ratAdd (ratMul (natRat 1) ratZero) (ratMul ratZero ratZero))))
        (ratMul (ratMul twoRat (ratNeg (natRat 193136)))
          (ratMul (natRat 1) ratZero)))
      (natRat 303318) at base
  exact base

theorem weil_offdiag_negative :
    ratLe (ratNeg (natRat 193136)) ratZero := by
  have hnonneg : ratLe ratZero (natRat 193136) :=
    natRat_large_nonneg 193136
  have raw : ratLe (ratAdd ratZero (ratNeg (natRat 193136))) ratZero :=
    ratSub_le_left_of_nonneg (x := ratZero) (y := natRat 193136) hnonneg
  exact ratLe_of_RatEq_left (RatEq_symm (ratZero_add_left (ratNeg (natRat 193136)))) raw

/-- Public bundled certificate: exact PSD, eigenvalue lower bound, diagonalization, and a negative entry. -/
theorem fibonacci_window_weil_matrix_positivity_certificate :
    (∀ x0 x1 x2 : Rat, ratLe ratZero (quadW x0 x1 x2)) ∧
      (∀ x0 x1 x2 : Rat,
        ratLe
          (ratMul lambdaW (norm3W x0 x1 x2))
          (quadW x0 x1 x2)) ∧
      (∀ x0 x1 x2 : Rat,
        RatEq (ratMul twoRat (quadW x0 x1 x2))
          (ratAdd (block2W x0 x1 x2) (block1W x0 x2))) ∧
      ratLe (ratNeg (natRat 193136)) ratZero := by
  constructor
  · intro x0 x1 x2
    exact weil_window3_matrix_psd x0 x1 x2
  · constructor
    · intro x0 x1 x2
      exact weil_window3_matrix_lower_bound x0 x1 x2
    · constructor
      · intro x0 x1 x2
        exact quadW_diagonalization x0 x1 x2
      · exact weil_offdiag_negative

#print axioms quadW_diagonalization
#print axioms two_quadW_nonneg
#print axioms weil_window3_matrix_psd
#print axioms shiftedQuadW_diagonalization
#print axioms shiftedQuadW_nonneg
#print axioms weil_window3_matrix_lower_bound
#print axioms fibonacci_window_weil_matrix_positivity_certificate

end BEDC.Derived.RHRoute.FibonacciWindowWeilMatrixPositivity
