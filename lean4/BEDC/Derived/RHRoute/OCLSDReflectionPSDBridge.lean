import BEDC.Derived.RHRoute.OCLSDReflectionForm
import BEDC.Derived.RHRoute.IntervalMatrixPSD

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

namespace BEDC.Derived.RHRoute.OCLSDReflectionPSDBridge

open BEDC.Algebra.FiniteFold
open BEDC.Algebra.Rel (RelCommRing)
open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumKernel
open BEDC.Derived.LocatedReal
  (ratAdd_assoc_local ratAdd_neg_local ratNeg_add_local ratNeg_neg_local
    ratNeg_add_dist_local)

/-!
OCLSD 的二态 reflection form 与共享 `psd_2x2` 检查器的同一化桥。

等式侧只在 located `RatEq` 层做有限交换环归一化；顺序侧只消费已有
`ratSub_nonneg_of_le`、`ratAdd_le_add` 与 `IntervalMatrixBEDC.Derived.RHRoute.IntervalMatrixPSD.psd_2x2`。
-/

private def ratRing : RelCommRing RatNum RatEq where
  zero := ratZero
  one := ratOne
  add := ratAdd
  mul := ratMul
  neg := ratNeg
  refl := RatEq_refl
  symm := by
    intro _ _
    exact RatEq_symm
  trans := by
    intro x y z
    exact RatEq_trans x y z
  add_congr := by
    intro _ _ _ _ hleft hright
    exact ratAdd_respects hleft hright
  mul_congr := by
    intro _ _ _ _ hleft hright
    exact ratMul_respects hleft hright
  neg_congr := by
    intro _ _ h
    exact ratNeg_respects h
  add_assoc := ratAdd_assoc_local
  add_comm := ratAdd_comm
  add_zero := ratAdd_zero_right
  zero_add := ratZero_add_left
  add_neg := ratAdd_neg_local
  neg_add := ratNeg_add_local
  mul_assoc := ratMul_assoc
  mul_one := ratMul_one_right
  one_mul := ratOne_mul_left
  mul_zero := BEDC.Derived.RHRoute.OCLSDReflectionForm.ratMul_zero_right
  zero_mul := BEDC.Derived.RHRoute.OCLSDReflectionForm.ratMul_zero_left
  left_distrib := ratMul_add_left
  right_distrib := ratMul_add_right
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

private def rExprEval (vars : Nat -> RatNum) : RExpr -> RatNum
  | RExpr.var i => vars i
  | RExpr.zero => ratZero
  | RExpr.one => ratOne
  | RExpr.add a b => ratAdd (rExprEval vars a) (rExprEval vars b)
  | RExpr.mul a b => ratMul (rExprEval vars a) (rExprEval vars b)
  | RExpr.neg a => ratNeg (rExprEval vars a)

private def rMonoEval (vars : Nat -> RatNum) : List Nat -> RatNum
  | [] => ratOne
  | i :: is => ratMul (vars i) (rMonoEval vars is)

private def rTermEval (vars : Nat -> RatNum) (t : RTerm) : RatNum :=
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

private def rSumTerms (vars : Nat -> RatNum) : List RTerm -> RatNum
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

private theorem rMonoEval_perm (vars : Nat -> RatNum) :
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

private theorem rTermCanonical_eval (vars : Nat -> RatNum) (t : RTerm) :
    RatEq (rTermEval vars (rTermCanonical t)) (rTermEval vars t) := by
  cases t with
  | mk isNeg mono =>
      cases isNeg
      · exact rMonoEval_perm vars (natSort_perm mono)
      · exact ratNeg_respects (rMonoEval_perm vars (natSort_perm mono))

private theorem rSum_canonical (vars : Nat -> RatNum) :
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

private theorem rSum_perm (vars : Nat -> RatNum) :
    ∀ {xs ys : List RTerm},
      ListPerm xs ys -> RatEq (rSumTerms vars xs) (rSumTerms vars ys)
  | _, _, ListPerm.nil =>
      RatEq_refl ratZero
  | _, _, ListPerm.cons x p => by
      exact ratAdd_respects (RatEq_refl (rTermEval vars x)) (rSum_perm vars p)
  | _, _, ListPerm.swap x y xs => by
      exact RatEq_trans _ _ _
        (RatEq_symm
          (ratAdd_assoc_local
            (rTermEval vars x) (rTermEval vars y) (rSumTerms vars xs)))
        (RatEq_trans _ _ _
          (ratAdd_respects
            (ratAdd_comm (rTermEval vars x) (rTermEval vars y))
            (RatEq_refl (rSumTerms vars xs)))
          (ratAdd_assoc_local
            (rTermEval vars y) (rTermEval vars x) (rSumTerms vars xs)))
  | _, _, ListPerm.trans p q =>
      RatEq_trans _ _ _ (rSum_perm vars p) (rSum_perm vars q)

private theorem rSum_sort (vars : Nat -> RatNum) (terms : List RTerm) :
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
    (vars : Nat -> RatNum) (t u : RTerm) :
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
            exact ratAdd_neg_local (rMonoEval vars uVars)
          · unfold rTermOppositeSame at h
            have sameVars := natListEqBool_eq_true tVars uVars h
            rw [sameVars]
            change RatEq
              (ratAdd (ratNeg (rMonoEval vars uVars)) (rMonoEval vars uVars))
              ratZero
            exact ratNeg_add_local (rMonoEval vars uVars)
          · cases h

private theorem rCancelStep_sound (vars : Nat -> RatNum) :
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
              (ratAdd_assoc_local
                (rTermEval vars t) (rTermEval vars u) (rSumTerms vars us)))
            (RatEq_trans _ _ _
              (ratAdd_respects (rTermOppositeSame_eval_zero vars t u h)
                (RatEq_refl (rSumTerms vars us)))
              (ratZero_add_left (rSumTerms vars us))))

private theorem rCancelGo_sound (vars : Nat -> RatNum) :
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
              (ratAdd_assoc_local
                (rSumTerms vars ts) (rTermEval vars t) (rSumTerms vars acc)))
            (ratAdd_respects
              (ratAdd_comm (rSumTerms vars ts) (rTermEval vars t))
              (RatEq_refl (rSumTerms vars acc)))))

private theorem rCancelTerms_sound (vars : Nat -> RatNum) (terms : List RTerm) :
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

private theorem rSum_append (vars : Nat -> RatNum) (xs ys : List RTerm) :
    RatEq (rSumTerms vars (xs ++ ys))
      (ratAdd (rSumTerms vars xs) (rSumTerms vars ys)) := by
  induction xs with
  | nil =>
      exact RatEq_symm (ratZero_add_left (rSumTerms vars ys))
  | cons x xs ih =>
      exact RatEq_trans _ _ _
        (ratAdd_respects (RatEq_refl (rTermEval vars x)) ih)
        (RatEq_symm
          (ratAdd_assoc_local
            (rTermEval vars x) (rSumTerms vars xs) (rSumTerms vars ys)))

private theorem rMonoEval_append (vars : Nat -> RatNum) :
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

private theorem rTermEval_neg (vars : Nat -> RatNum) (t : RTerm) :
    RatEq (rTermEval vars (rTermNeg t)) (ratNeg (rTermEval vars t)) := by
  cases t with
  | mk isNeg mono =>
      cases isNeg
      · exact RatEq_refl (ratNeg (rMonoEval vars mono))
      · exact RatEq_symm (ratNeg_neg_local (rMonoEval vars mono))

private theorem rTermEval_mul (vars : Nat -> RatNum) (t u : RTerm) :
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

private theorem rSum_neg (vars : Nat -> RatNum) :
    ∀ terms : List RTerm,
      RatEq (rSumTerms vars (List.map rTermNeg terms))
        (ratNeg (rSumTerms vars terms))
  | [] => by
      exact RatEq_symm ratRing.neg_zero
  | t :: ts => by
      exact RatEq_trans _ _ _
        (ratAdd_respects (rTermEval_neg vars t) (rSum_neg vars ts))
        (RatEq_symm
          (ratNeg_add_dist_local (rTermEval vars t) (rSumTerms vars ts)))

private theorem rTermsMulOne_sound (vars : Nat -> RatNum) (t : RTerm) :
    ∀ terms : List RTerm,
      RatEq (rSumTerms vars (rTermsMulOne t terms))
        (ratMul (rTermEval vars t) (rSumTerms vars terms))
  | [] => by
      exact RatEq_symm (BEDC.Derived.RHRoute.OCLSDReflectionForm.ratMul_zero_right (rTermEval vars t))
  | u :: us => by
      exact RatEq_trans _ _ _
        (ratAdd_respects (rTermEval_mul vars t u)
          (rTermsMulOne_sound vars t us))
        (RatEq_symm
          (ratMul_add_left
            (rTermEval vars t) (rTermEval vars u) (rSumTerms vars us)))

private theorem rTermsMul_sound (vars : Nat -> RatNum) :
    ∀ xs ys : List RTerm,
      RatEq (rSumTerms vars (rTermsMul xs ys))
        (ratMul (rSumTerms vars xs) (rSumTerms vars ys))
  | [], ys => by
      exact RatEq_symm (BEDC.Derived.RHRoute.OCLSDReflectionForm.ratMul_zero_left (rSumTerms vars ys))
  | x :: xs, ys => by
      exact RatEq_trans _ _ _
        (rSum_append vars (rTermsMulOne x ys) (rTermsMul xs ys))
        (RatEq_trans _ _ _
          (ratAdd_respects
            (rTermsMulOne_sound vars x ys)
            (rTermsMul_sound vars xs ys))
          (RatEq_symm
            (ratMul_add_right
              (rTermEval vars x) (rSumTerms vars xs) (rSumTerms vars ys))))

private theorem rExprTerms_sound :
    ∀ (vars : Nat -> RatNum) (e : RExpr),
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

private theorem rExprNorm_sound (vars : Nat -> RatNum) (e : RExpr) :
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

private theorem rExpr_same_norm (vars : Nat -> RatNum) (a b : RExpr)
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

private def rSq (x : RExpr) : RExpr :=
  rMul x x

private def rTwo : RExpr :=
  rAdd RExpr.one RExpr.one

private def qE : RExpr := rV 0
private def f0E : RExpr := rV 1
private def f1E : RExpr := rV 2
private def x2E : RExpr := rSq f0E
private def y2E : RExpr := rSq f1E
private def xyE : RExpr := rMul f0E f1E
private def omtE : RExpr := rSub RExpr.one (rMul rTwo qE)
private def omqE : RExpr := rSub RExpr.one qE

private def osFormExpr : RExpr :=
  rAdd
    (rMul qE (rSq (rAdd f0E f1E)))
    (rMul omtE (rAdd (rSq f0E) (rSq f1E)))

private def osFormRawExpr : RExpr :=
  rAdd
    (rAdd
      (rAdd
        (rMul qE x2E)
        (rAdd (rMul qE xyE) (rMul qE xyE)))
      (rMul qE y2E))
    (rAdd
      (rMul omtE x2E)
      (rMul omtE y2E))

private def psdQuadExpr : RExpr :=
  rAdd
    (rAdd
      (rMul omqE x2E)
      (rMul (rMul rTwo qE) xyE))
    (rMul omqE y2E)

private theorem osForm_expand_raw_norm :
    rExprNorm osFormExpr = rExprNorm osFormRawExpr :=
  rfl

private theorem osForm_raw_psd_norm :
    rExprNorm osFormRawExpr = rExprNorm psdQuadExpr :=
  rfl

private def collect5Left : RExpr :=
  rAdd (rAdd (rAdd (rV 0) (rV 1)) (rV 2)) (rAdd (rV 3) (rV 4))

private def collect5Right : RExpr :=
  rAdd (rAdd (rAdd (rV 0) (rV 3)) (rV 1)) (rAdd (rV 2) (rV 4))

/-- 五项加法的 located 重排。 -/
theorem ratAdd_collect_5 (a b c d e : RatNum) :
    RatEq
      (ratAdd (ratAdd (ratAdd a b) c) (ratAdd d e))
      (ratAdd (ratAdd (ratAdd a d) b) (ratAdd c e)) := by
  let vars : Nat -> RatNum := fun
    | 0 => a
    | 1 => b
    | 2 => c
    | 3 => d
    | _ => e
  have base :
      RatEq (rExprEval vars collect5Left) (rExprEval vars collect5Right) :=
    rExpr_same_norm vars collect5Left collect5Right rfl
  change RatEq (rExprEval vars collect5Left) (rExprEval vars collect5Right)
  exact base

private def twoCoeffLeft : RExpr :=
  rAdd (rV 0) (rV 0)

private def twoCoeffRight : RExpr :=
  rMul rTwo (rV 0)

/-- `q + q = 2q`, with the `2` used by `IntervalMatrixPSD`. -/
theorem rat_two_mul_coeff (q : RatNum) :
    RatEq (ratAdd q q) (ratMul (BEDC.Derived.RHRoute.IntervalMatrixPSD.natRat 2) q) := by
  let vars : Nat -> RatNum := fun _ => q
  have base :
      RatEq (rExprEval vars twoCoeffLeft) (rExprEval vars twoCoeffRight) :=
    rExpr_same_norm vars twoCoeffLeft twoCoeffRight rfl
  unfold BEDC.Derived.RHRoute.IntervalMatrixPSD.natRat
  change RatEq (rExprEval vars twoCoeffLeft) (rExprEval vars twoCoeffRight)
  exact base

private def qAddOmtLeft : RExpr :=
  rAdd qE omtE

private def qAddOmtRight : RExpr :=
  omqE

/-- `q + (1 - 2q) = 1 - q`. -/
theorem q_add_oneMinusTwoQ_eq_oneMinusQ (q : RatNum) :
    RatEq
      (ratAdd q (BEDC.Derived.RHRoute.OCLSDReflectionForm.oneMinusTwoQ q))
      (ratSub ratOne q) := by
  let vars : Nat -> RatNum := fun _ => q
  have base :
      RatEq (rExprEval vars qAddOmtLeft) (rExprEval vars qAddOmtRight) :=
    rExpr_same_norm vars qAddOmtLeft qAddOmtRight rfl
  unfold BEDC.Derived.RHRoute.OCLSDReflectionForm.oneMinusTwoQ BEDC.Derived.RHRoute.OCLSDReflectionForm.twoRat ratSub
  change RatEq (rExprEval vars qAddOmtLeft) (rExprEval vars qAddOmtRight)
  exact base

private def detGapLeft : RExpr :=
  rSub (rMul omqE omqE) (rMul qE qE)

private def detGapRight : RExpr :=
  omtE

/-- `(1 - q)^2 - q^2 = 1 - 2q`. -/
theorem detGap (q : RatNum) :
    RatEq
      (ratSub
        (ratMul (ratSub ratOne q) (ratSub ratOne q))
        (ratMul q q))
      (BEDC.Derived.RHRoute.OCLSDReflectionForm.oneMinusTwoQ q) := by
  let vars : Nat -> RatNum := fun _ => q
  have base :
      RatEq (rExprEval vars detGapLeft) (rExprEval vars detGapRight) :=
    rExpr_same_norm vars detGapLeft detGapRight rfl
  unfold BEDC.Derived.RHRoute.OCLSDReflectionForm.oneMinusTwoQ BEDC.Derived.RHRoute.OCLSDReflectionForm.twoRat ratSub
  change RatEq (rExprEval vars detGapLeft) (rExprEval vars detGapRight)
  exact base

/-- `a ≤ b` 的 located 差值非负形式。 -/
theorem ratSub_nonneg_of_ratLe {a b : RatNum}
    (h : ratLe a b) :
    ratLe ratZero (ratSub b a) :=
  ratSub_nonneg_of_le h

/-- located 非负数对加法封闭。 -/
theorem ratLe_add_nonneg {a b : RatNum}
    (ha : ratLe ratZero a)
    (hb : ratLe ratZero b) :
    ratLe ratZero (ratAdd a b) := by
  have raw :
      ratLe (ratAdd ratZero ratZero) (ratAdd a b) :=
    ratAdd_le_add ha hb
  exact ratLe_of_RatEq_left (RatEq_symm (ratZero_add_left ratZero)) raw

abbrev psdQuad (q f0 f1 : RatNum) : RatNum :=
  ratAdd
    (ratAdd
      (ratMul (ratSub ratOne q) (ratMul f0 f0))
      (ratMul (ratMul (BEDC.Derived.RHRoute.IntervalMatrixPSD.natRat 2) q) (ratMul f0 f1)))
    (ratMul (ratSub ratOne q) (ratMul f1 f1))

private def osFormRaw (q f0 f1 : RatNum) : RatNum :=
  ratAdd
    (ratAdd
      (ratAdd
        (ratMul q (ratMul f0 f0))
        (ratAdd
          (ratMul q (ratMul f0 f1))
          (ratMul q (ratMul f0 f1))))
      (ratMul q (ratMul f1 f1)))
    (ratAdd
      (ratMul (BEDC.Derived.RHRoute.OCLSDReflectionForm.oneMinusTwoQ q) (ratMul f0 f0))
      (ratMul (BEDC.Derived.RHRoute.OCLSDReflectionForm.oneMinusTwoQ q) (ratMul f1 f1)))

private theorem osForm_expand_raw (q f0 f1 : RatNum) :
    RatEq (BEDC.Derived.RHRoute.OCLSDReflectionForm.osForm q f0 f1) (osFormRaw q f0 f1) := by
  let vars : Nat -> RatNum := fun
    | 0 => q
    | 1 => f0
    | _ => f1
  have base :
      RatEq (rExprEval vars osFormExpr) (rExprEval vars osFormRawExpr) :=
    rExpr_same_norm vars osFormExpr osFormRawExpr osForm_expand_raw_norm
  unfold BEDC.Derived.RHRoute.OCLSDReflectionForm.osForm BEDC.Derived.RHRoute.OCLSDReflectionForm.ratSq BEDC.Derived.RHRoute.OCLSDReflectionForm.oneMinusTwoQ BEDC.Derived.RHRoute.OCLSDReflectionForm.twoRat osFormRaw ratSub
  change RatEq (rExprEval vars osFormExpr) (rExprEval vars osFormRawExpr)
  exact base

private theorem cross_collect (q xy : RatNum) :
    RatEq
      (ratAdd (ratMul q xy) (ratMul q xy))
      (ratMul (ratMul (BEDC.Derived.RHRoute.IntervalMatrixPSD.natRat 2) q) xy) :=
  RatEq_trans _ _ _
    (RatEq_symm (ratMul_add_right q q xy))
    (ratMul_respects (rat_two_mul_coeff q) (RatEq_refl xy))

private theorem collect_q_omt_right (q z : RatNum) :
    RatEq
      (ratAdd
        (ratMul q z)
        (ratMul (BEDC.Derived.RHRoute.OCLSDReflectionForm.oneMinusTwoQ q) z))
      (ratMul (ratSub ratOne q) z) :=
  RatEq_trans _ _ _
    (RatEq_symm (ratMul_add_right q (BEDC.Derived.RHRoute.OCLSDReflectionForm.oneMinusTwoQ q) z))
    (ratMul_respects
      (q_add_oneMinusTwoQ_eq_oneMinusQ q)
      (RatEq_refl z))

private theorem osForm_expanded_raw_eq_psdQuad (q f0 f1 : RatNum) :
    RatEq (osFormRaw q f0 f1) (psdQuad q f0 f1) := by
  let x2 := ratMul f0 f0
  let y2 := ratMul f1 f1
  let xy := ratMul f0 f1
  have hperm :
      RatEq
        (ratAdd
          (ratAdd
            (ratAdd
              (ratMul q x2)
              (ratAdd (ratMul q xy) (ratMul q xy)))
            (ratMul q y2))
          (ratAdd
            (ratMul (BEDC.Derived.RHRoute.OCLSDReflectionForm.oneMinusTwoQ q) x2)
            (ratMul (BEDC.Derived.RHRoute.OCLSDReflectionForm.oneMinusTwoQ q) y2)))
        (ratAdd
          (ratAdd
            (ratAdd
              (ratMul q x2)
              (ratMul (BEDC.Derived.RHRoute.OCLSDReflectionForm.oneMinusTwoQ q) x2))
            (ratAdd (ratMul q xy) (ratMul q xy)))
          (ratAdd
            (ratMul q y2)
            (ratMul (BEDC.Derived.RHRoute.OCLSDReflectionForm.oneMinusTwoQ q) y2))) :=
    ratAdd_collect_5
      (ratMul q x2)
      (ratAdd (ratMul q xy) (ratMul q xy))
      (ratMul q y2)
      (ratMul (BEDC.Derived.RHRoute.OCLSDReflectionForm.oneMinusTwoQ q) x2)
      (ratMul (BEDC.Derived.RHRoute.OCLSDReflectionForm.oneMinusTwoQ q) y2)
  have hcollect :
      RatEq
        (ratAdd
          (ratAdd
            (ratAdd
              (ratMul q x2)
              (ratMul (BEDC.Derived.RHRoute.OCLSDReflectionForm.oneMinusTwoQ q) x2))
            (ratAdd (ratMul q xy) (ratMul q xy)))
          (ratAdd
            (ratMul q y2)
            (ratMul (BEDC.Derived.RHRoute.OCLSDReflectionForm.oneMinusTwoQ q) y2)))
        (ratAdd
          (ratAdd
            (ratMul (ratSub ratOne q) x2)
            (ratMul (ratMul (BEDC.Derived.RHRoute.IntervalMatrixPSD.natRat 2) q) xy))
          (ratMul (ratSub ratOne q) y2)) :=
    ratAdd_respects
      (ratAdd_respects
        (collect_q_omt_right q x2)
        (cross_collect q xy))
      (collect_q_omt_right q y2)
  exact RatEq_trans _ _ _ hperm hcollect

/-- OCLSD reflection form is the shared 2x2 PSD quadratic form. -/
theorem osForm_eq_psd2x2 (q f0 f1 : RatNum) :
    RatEq (BEDC.Derived.RHRoute.OCLSDReflectionForm.osForm q f0 f1) (psdQuad q f0 f1) :=
  RatEq_trans _ _ _
    (osForm_expand_raw q f0 f1)
    (osForm_expanded_raw_eq_psdQuad q f0 f1)

private theorem omq_eq_omt_add_q (q : RatNum) :
    RatEq
      (ratSub ratOne q)
      (ratAdd (BEDC.Derived.RHRoute.OCLSDReflectionForm.oneMinusTwoQ q) q) :=
  RatEq_trans _ _ _
    (RatEq_symm (q_add_oneMinusTwoQ_eq_oneMinusQ q))
    (ratAdd_comm q (BEDC.Derived.RHRoute.OCLSDReflectionForm.oneMinusTwoQ q))

private theorem oneMinusTwoQ_nonneg_of_RP (q : RatNum)
    (hq : ratLe (ratMul BEDC.Derived.RHRoute.OCLSDReflectionForm.twoRat q) ratOne) :
    ratLe ratZero (BEDC.Derived.RHRoute.OCLSDReflectionForm.oneMinusTwoQ q) := by
  unfold BEDC.Derived.RHRoute.OCLSDReflectionForm.oneMinusTwoQ
  exact ratSub_nonneg_of_ratLe hq

private theorem oneMinusQ_nonneg_of_RP (q : RatNum)
    (hq0 : ratLe ratZero q)
    (hq : ratLe (ratMul BEDC.Derived.RHRoute.OCLSDReflectionForm.twoRat q) ratOne) :
    ratLe ratZero (ratSub ratOne q) := by
  have h1m2q : ratLe ratZero (BEDC.Derived.RHRoute.OCLSDReflectionForm.oneMinusTwoQ q) :=
    oneMinusTwoQ_nonneg_of_RP q hq
  have hsum :
      ratLe ratZero (ratAdd (BEDC.Derived.RHRoute.OCLSDReflectionForm.oneMinusTwoQ q) q) :=
    ratLe_add_nonneg h1m2q hq0
  exact ratLe_of_RatEq_right hsum (RatEq_symm (omq_eq_omt_add_q q))

private theorem det_condition_of_RP (q : RatNum)
    (hq : ratLe (ratMul BEDC.Derived.RHRoute.OCLSDReflectionForm.twoRat q) ratOne) :
    ratLe
      (ratMul q q)
      (ratMul (ratSub ratOne q) (ratSub ratOne q)) := by
  have h1m2q : ratLe ratZero (BEDC.Derived.RHRoute.OCLSDReflectionForm.oneMinusTwoQ q) :=
    oneMinusTwoQ_nonneg_of_RP q hq
  have hgap :
      ratLe ratZero
        (ratSub
          (ratMul (ratSub ratOne q) (ratSub ratOne q))
          (ratMul q q)) :=
    ratLe_of_RatEq_right h1m2q (RatEq_symm (detGap q))
  exact BEDC.Derived.RHRoute.OCLSDReflectionForm.ratLe_of_sub_nonneg
    (ratMul q q)
    (ratMul (ratSub ratOne q) (ratSub ratOne q))
    hgap

/-- RP lane 的条件通过同一个 `psd_2x2` checker 给出 OCLSD reflection positivity。 -/
theorem reflection_holds_via_psd
    (q f0 f1 : RatNum)
    (hq0 : ratLe ratZero q)
    (hq : ratLe (ratMul BEDC.Derived.RHRoute.OCLSDReflectionForm.twoRat q) ratOne) :
    ratLe ratZero (BEDC.Derived.RHRoute.OCLSDReflectionForm.osForm q f0 f1) := by
  let b : RatNum := ratSub ratOne q
  have h11 : ratLe ratZero b :=
    oneMinusQ_nonneg_of_RP q hq0 hq
  have h22 : ratLe ratZero b := h11
  have hdet : ratLe (ratMul q q) (ratMul b b) :=
    det_condition_of_RP q hq
  have hpsd : ratLe ratZero (psdQuad q f0 f1) := by
    unfold psdQuad
    change
      ratLe ratZero
        (ratAdd
          (ratAdd
            (ratMul b (ratMul f0 f0))
            (ratMul (ratMul (BEDC.Derived.RHRoute.IntervalMatrixPSD.natRat 2) q) (ratMul f0 f1)))
          (ratMul b (ratMul f1 f1)))
    exact BEDC.Derived.RHRoute.IntervalMatrixPSD.psd_2x2 b q b h11 h22 hdet f0 f1
  exact ratLe_of_RatEq_right hpsd
    (RatEq_symm (osForm_eq_psd2x2 q f0 f1))

end BEDC.Derived.RHRoute.OCLSDReflectionPSDBridge
