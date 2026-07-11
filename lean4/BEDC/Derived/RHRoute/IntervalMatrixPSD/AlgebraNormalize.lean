import BEDC.Algebra.FiniteFold
import BEDC.Derived.RHRoute.IntervalMatrixPSD.RatRingCanonical
import BEDC.Real.RatNumKernel

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

namespace BEDC.Derived.RHRoute.IntervalMatrixPSD

open BEDC.Algebra.Rel (RelCommRing)
open BEDC.Algebra.FiniteFold
open BEDC.Derived.RationalUp

private theorem ratMul_zero_right_local (x : Rat) :
    RatEq (ratMul x ratZero) ratZero := by
  unfold RatEq ratMul ratZero intToRat
  change
    IntEq (IntMul (IntMul x.num intZero) (ratDenInt ratZero))
      (IntMul intZero (ratDenInt (ratMul x ratZero)))
  exact IntEq_trans (intMul_right_congr (intMul_zero_right x.num))
    (IntEq_symm (intMul_zero_left (ratDenInt (ratMul x ratZero))))

private theorem ratMul_zero_left_local (x : Rat) :
    RatEq (ratMul ratZero x) ratZero :=
  RatEq_trans _ _ _ (ratMul_comm ratZero x) (ratMul_zero_right_local x)

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
              (RatEq_symm (ratRingCanonical.mul_neg (rMonoEval vars tVars)
                (rMonoEval vars uVars)))
          · exact RatEq_trans _ _ _
              (ratNeg_respects (rMonoEval_append vars tVars uVars))
              (RatEq_symm (ratRingCanonical.neg_mul (rMonoEval vars tVars)
                (rMonoEval vars uVars)))
          · exact RatEq_trans _ _ _
              (rMonoEval_append vars tVars uVars)
              (RatEq_symm (ratRingCanonical.neg_neg_mul_neg
                (rMonoEval vars tVars) (rMonoEval vars uVars)))

private theorem rSum_neg (vars : Nat -> Rat) :
    ∀ terms : List RTerm,
      RatEq (rSumTerms vars (List.map rTermNeg terms))
        (ratNeg (rSumTerms vars terms))
  | [] => by
      exact RatEq_symm ratRingCanonical.neg_zero
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

private def qExpr : RExpr :=
  rAdd
    (rAdd
      (rMul (rV 0) (rMul (rV 3) (rV 3)))
      (rMul (rMul rTwo (rV 1)) (rMul (rV 3) (rV 4))))
    (rMul (rV 2) (rMul (rV 4) (rV 4)))

private def squareBridgeLeft : RExpr :=
  rMul (rV 0) qExpr

private def squareBridgeRight : RExpr :=
  rAdd
    (rMul (rAdd (rMul (rV 0) (rV 3)) (rMul (rV 1) (rV 4)))
      (rAdd (rMul (rV 0) (rV 3)) (rMul (rV 1) (rV 4))))
    (rMul (rSub (rMul (rV 0) (rV 2)) (rMul (rV 1) (rV 1)))
      (rMul (rV 4) (rV 4)))

private theorem square_bridge_expr_norm :
    rExprNorm squareBridgeLeft = rExprNorm squareBridgeRight :=
  rfl

theorem complete_square_identity
    (b11 b12 b22 c1 c2 : Rat) :
    RatEq
      (ratMul b11
        (ratAdd
          (ratAdd
            (ratMul b11 (ratMul c1 c1))
            (ratMul (ratMul (natRat 2) b12) (ratMul c1 c2)))
          (ratMul b22 (ratMul c2 c2))))
      (ratAdd
        (ratMul
          (ratAdd (ratMul b11 c1) (ratMul b12 c2))
          (ratAdd (ratMul b11 c1) (ratMul b12 c2)))
        (ratMul
          (ratSub (ratMul b11 b22) (ratMul b12 b12))
          (ratMul c2 c2))) := by
  let vars : Nat -> Rat := fun
    | 0 => b11
    | 1 => b12
    | 2 => b22
    | 3 => c1
    | _ => c2
  have base :
      RatEq (rExprEval vars squareBridgeLeft)
        (rExprEval vars squareBridgeRight) :=
    rExpr_same_norm vars squareBridgeLeft squareBridgeRight square_bridge_expr_norm
  change
    RatEq
      (ratMul b11
        (ratAdd
          (ratAdd
            (ratMul b11 (ratMul c1 c1))
            (ratMul (ratMul (ratAdd ratOne ratOne) b12)
              (ratMul c1 c2)))
          (ratMul b22 (ratMul c2 c2))))
      (ratAdd
        (ratMul
          (ratAdd (ratMul b11 c1) (ratMul b12 c2))
          (ratAdd (ratMul b11 c1) (ratMul b12 c2)))
        (ratMul
          (ratAdd (ratMul b11 b22) (ratNeg (ratMul b12 b12)))
          (ratMul c2 c2))) at base
  exact base

end BEDC.Derived.RHRoute.IntervalMatrixPSD
