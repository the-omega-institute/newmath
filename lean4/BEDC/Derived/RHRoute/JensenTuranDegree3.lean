import BEDC.Derived.RHRoute.IntervalMatrixPSD.AlgebraNormalize
import BEDC.Derived.RHRoute.JensenTuranDegree2

namespace BEDC.Derived.RHRoute.JensenTuranDegree3

open BEDC.Algebra.Rel (RelCommRing)
open BEDC.Algebra.FiniteFold
open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp

abbrev Rat : Type :=
  RatNum

private def ratTwoC : Rat :=
  ratAdd ratOne ratOne

private def ratFourC : Rat :=
  ratAdd ratTwoC ratTwoC

private def ratThreeC : Rat :=
  ratSub ratFourC ratOne

private def ratSixC : Rat :=
  ratAdd ratThreeC ratThreeC

private def ratTwelveC : Rat :=
  ratAdd ratSixC ratSixC

private def ratElevenC : Rat :=
  ratSub ratTwelveC ratOne

private def ratEighteenC : Rat :=
  ratAdd ratTwelveC ratSixC

private def ratTwentySevenC : Rat :=
  BEDC.Real.RatNumKernel.ratNat 27

private def ratThreeHundredTwentyFourC : Rat :=
  ratMul ratTwentySevenC ratTwelveC

private def ratEightyOneC : Rat :=
  ratMul ratTwentySevenC ratThreeC

private def ratHundredEightC : Rat :=
  ratMul ratTwentySevenC ratFourC

private def ratHundredSixtyTwoC : Rat :=
  ratMul ratTwentySevenC (ratAdd ratFourC ratTwoC)

def natRat : Nat -> Rat
  | 0 => ratZero
  | 1 => ratOne
  | 2 => ratTwoC
  | 3 => ratThreeC
  | 4 => ratFourC
  | 6 => ratSixC
  | 11 => ratElevenC
  | 12 => ratTwelveC
  | 18 => ratEighteenC
  | 27 => ratTwentySevenC
  | 81 => ratEightyOneC
  | 108 => ratHundredEightC
  | 162 => ratHundredSixtyTwoC
  | 324 => ratThreeHundredTwentyFourC
  | Nat.succ n => ratAdd ratOne (natRat n)

def ratCube (x : Rat) : Rat :=
  ratMul x (ratMul x x)

def jensen3 (g0 g1 g2 g3 X : Rat) : Rat :=
  ratAdd
    (ratAdd
      (ratAdd g0 (ratMul (ratMul (natRat 3) g1) X))
      (ratMul (ratMul (natRat 3) g2) (ratMul X X)))
    (ratMul g3 (ratCube X))

def turanA (g0 g1 g2 _g3 : Rat) : Rat :=
  ratSub (ratMul g1 g1) (ratMul g0 g2)

def turanB (_g0 g1 g2 g3 : Rat) : Rat :=
  ratSub (ratMul g2 g2) (ratMul g1 g3)

def turanC (g0 g1 g2 g3 : Rat) : Rat :=
  ratSub (ratMul g1 g2) (ratMul g0 g3)

def turanT3 (g0 g1 g2 g3 : Rat) : Rat :=
  ratSub
    (ratMul (natRat 4)
      (ratMul (turanA g0 g1 g2 g3) (turanB g0 g1 g2 g3)))
    (ratMul (turanC g0 g1 g2 g3) (turanC g0 g1 g2 g3))

def subdiscHA (g0 g1 g2 g3 : Rat) : Rat :=
  ratAdd
    (ratSub
      (ratMul (natRat 2) (ratCube g1))
      (ratMul (natRat 3) (ratMul (ratMul g0 g1) g2)))
    (ratMul (ratMul g0 g0) g3)

def subdiscHB (g0 g1 g2 g3 : Rat) : Rat :=
  ratAdd
    (ratSub
      (ratMul (natRat 2) (ratCube g2))
      (ratMul (natRat 3) (ratMul (ratMul g1 g2) g3)))
    (ratMul g0 (ratMul g3 g3))

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

private abbrev ratRing : RelCommRing Rat RatEq :=
  BEDC.Derived.RHRoute.IntervalMatrixPSD.ratRelCommRing

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

private def rFour : RExpr :=
  rV 4

private def rThree : RExpr :=
  rSub rFour RExpr.one

private def rTwentySeven : RExpr :=
  rV 5

private def rEightyOne : RExpr :=
  rMul rTwentySeven rThree

private def rHundredEight : RExpr :=
  rMul rTwentySeven rFour

private def rHundredSixtyTwo : RExpr :=
  rMul rTwentySeven (rAdd rFour rTwo)

private def rNat : Nat -> RExpr
  | 0 => RExpr.zero
  | 1 => RExpr.one
  | 2 => rTwo
  | 3 => rThree
  | 4 => rFour
  | 27 => rTwentySeven
  | 81 => rEightyOne
  | 108 => rHundredEight
  | 162 => rHundredSixtyTwo
  | Nat.succ n => rAdd RExpr.one (rNat n)

private def rSq (x : RExpr) : RExpr :=
  rMul x x

private def rCube (x : RExpr) : RExpr :=
  rMul x (rMul x x)

private def rA : RExpr :=
  rSub (rSq (rV 1)) (rMul (rV 0) (rV 2))

private def rB : RExpr :=
  rSub (rSq (rV 2)) (rMul (rV 1) (rV 3))

private def rC : RExpr :=
  rSub (rMul (rV 1) (rV 2)) (rMul (rV 0) (rV 3))

private def rT3 : RExpr :=
  rSub (rMul (rNat 4) (rMul rA rB)) (rSq rC)

private def rFourLiteral : RExpr :=
  rAdd rTwo rTwo

private def rThreeLiteral : RExpr :=
  rSub rFourLiteral RExpr.one

private def rT3Literal : RExpr :=
  rSub (rMul rFourLiteral (rMul rA rB)) (rSq rC)

private def rDelta : RExpr :=
  rAdd
    (rAdd
      (rAdd
        (rMul (rNat 81) (rMul (rSq (rV 1)) (rSq (rV 2))))
        (rNeg (rMul (rNat 108) (rMul (rCube (rV 1)) (rV 3)))))
      (rNeg (rMul (rNat 108) (rMul (rV 0) (rCube (rV 2))))))
    (rAdd
      (rNeg (rMul (rNat 27) (rMul (rSq (rV 0)) (rSq (rV 3)))))
      (rMul (rNat 162)
        (rMul (rMul (rV 0) (rV 1)) (rMul (rV 2) (rV 3)))))

private def rHA : RExpr :=
  rAdd
    (rSub
      (rMul (rNat 2) (rCube (rV 1)))
      (rMul (rNat 3) (rMul (rMul (rV 0) (rV 1)) (rV 2))))
    (rMul (rSq (rV 0)) (rV 3))

private def rHB : RExpr :=
  rAdd
    (rSub
      (rMul (rNat 2) (rCube (rV 2)))
      (rMul (rNat 3) (rMul (rMul (rV 1) (rV 2)) (rV 3))))
    (rMul (rV 0) (rSq (rV 3)))

private def rHALiteral : RExpr :=
  rAdd
    (rSub
      (rMul rTwo (rCube (rV 1)))
      (rMul rThreeLiteral (rMul (rMul (rV 0) (rV 1)) (rV 2))))
    (rMul (rSq (rV 0)) (rV 3))

private def rHBLiteral : RExpr :=
  rAdd
    (rSub
      (rMul rTwo (rCube (rV 2)))
      (rMul rThreeLiteral (rMul (rMul (rV 1) (rV 2)) (rV 3))))
    (rMul (rV 0) (rSq (rV 3)))

private def coeffVars (g0 g1 g2 g3 : Rat) : Nat -> Rat
  | 0 => g0
  | 1 => g1
  | 2 => g2
  | 3 => g3
  | 4 => natRat 4
  | 5 => natRat 27
  | _ => ratZero

def cubicDiscriminant (g0 g1 g2 g3 : Rat) : Rat :=
  rExprEval (coeffVars g0 g1 g2 g3) rDelta

private theorem cubic_discriminant_expr_norm :
    rExprNorm rDelta = rExprNorm (rMul (rNat 27) rT3) :=
  rfl

theorem cubic_discriminant_eq_27_T3 (g0 g1 g2 g3 : Rat) :
    RatEq (cubicDiscriminant g0 g1 g2 g3)
      (ratMul (natRat 27) (turanT3 g0 g1 g2 g3)) := by
  let vars := coeffVars g0 g1 g2 g3
  have h := rExpr_same_norm vars rDelta (rMul (rNat 27) rT3)
    cubic_discriminant_expr_norm
  change RatEq (cubicDiscriminant g0 g1 g2 g3)
    (ratMul (natRat 27) (turanT3 g0 g1 g2 g3)) at h
  exact h

private theorem subdiscriminant_A_expr_norm :
    rExprNorm (rMul rFourLiteral (rCube rA)) =
      rExprNorm (rAdd (rSq rHALiteral) (rMul (rSq (rV 0)) rT3Literal)) :=
  rfl

theorem subdiscriminant_A (g0 g1 g2 g3 : Rat) :
    RatEq
      (ratMul (natRat 4) (ratCube (turanA g0 g1 g2 g3)))
      (ratAdd
        (ratMul (subdiscHA g0 g1 g2 g3) (subdiscHA g0 g1 g2 g3))
        (ratMul (ratMul g0 g0) (turanT3 g0 g1 g2 g3))) := by
  let vars := coeffVars g0 g1 g2 g3
  have h := rExpr_same_norm vars
    (rMul rFourLiteral (rCube rA))
    (rAdd (rSq rHALiteral) (rMul (rSq (rV 0)) rT3Literal))
    subdiscriminant_A_expr_norm
  change
    RatEq
      (ratMul (natRat 4) (ratCube (turanA g0 g1 g2 g3)))
      (ratAdd
        (ratMul (subdiscHA g0 g1 g2 g3) (subdiscHA g0 g1 g2 g3))
        (ratMul (ratMul g0 g0) (turanT3 g0 g1 g2 g3))) at h
  exact h

private theorem subdiscriminant_B_expr_norm :
    rExprNorm (rMul rFourLiteral (rCube rB)) =
      rExprNorm (rAdd (rSq rHBLiteral) (rMul (rSq (rV 3)) rT3Literal)) :=
  rfl

theorem subdiscriminant_B (g0 g1 g2 g3 : Rat) :
    RatEq
      (ratMul (natRat 4) (ratCube (turanB g0 g1 g2 g3)))
      (ratAdd
        (ratMul (subdiscHB g0 g1 g2 g3) (subdiscHB g0 g1 g2 g3))
        (ratMul (ratMul g3 g3) (turanT3 g0 g1 g2 g3))) := by
  let vars := coeffVars g0 g1 g2 g3
  have h := rExpr_same_norm vars
    (rMul rFourLiteral (rCube rB))
    (rAdd (rSq rHBLiteral) (rMul (rSq (rV 3)) rT3Literal))
    subdiscriminant_B_expr_norm
  change
    RatEq
      (ratMul (natRat 4) (ratCube (turanB g0 g1 g2 g3)))
      (ratAdd
        (ratMul (subdiscHB g0 g1 g2 g3) (subdiscHB g0 g1 g2 g3))
        (ratMul (ratMul g3 g3) (turanT3 g0 g1 g2 g3))) at h
  exact h

private theorem intNatLeBool_true_to_le {a b : Nat} :
    BEDC.Derived.IntUp.natLeBool a b = true -> a ≤ b := by
  induction a generalizing b with
  | zero =>
      intro _h
      exact Nat.zero_le b
  | succ a ih =>
      intro h
      cases b with
      | zero =>
          cases h
      | succ b =>
          exact Nat.succ_le_succ (ih h)

private theorem ratLtBool_true_to_ratLt_local {x y : Rat} :
    ratLtBool x y = true -> ratLt x y := by
  intro h
  unfold ratLtBool at h
  unfold ratLt BEDC.Derived.RationalUp.intLtUp BEDC.Derived.IntUp.intLt
  exact Nat.lt_of_succ_le (intNatLeBool_true_to_le h)

private theorem natRat_four_pos :
    ratLt ratZero (natRat 4) := by
  apply ratLtBool_true_to_ratLt_local
  rfl

theorem ratMul_self_nonneg (x : Rat) :
    ratLe ratZero (ratMul x x) :=
  BEDC.Derived.RHRoute.JensenTuranDegree2.ratMul_self_nonneg x

private theorem ratNeg_pos_of_neg {x : Rat} :
    ratLt x ratZero -> ratLt ratZero (ratNeg x) := by
  intro h
  have subPos : ratLt ratZero (ratSub ratZero x) :=
    sub_pos_of_lt h
  exact BEDC.Real.RatNumKernel.ratLt_of_RatEq_right
    subPos
    (BEDC.Derived.LocatedReal.ratZero_sub_eq_neg x)

private theorem ratAdd_nonneg_local {x y : Rat} :
    ratLe ratZero x -> ratLe ratZero y -> ratLe ratZero (ratAdd x y) := by
  intro hx hy
  have raw :
      ratLe (ratAdd ratZero ratZero) (ratAdd x y) :=
    BEDC.Real.RatNumKernel.ratAdd_le_add hx hy
  exact ratLe_respects (ratZero_add_left ratZero) (RatEq_refl _) raw

private theorem ratMul_le_cancel_left_pos {a b c : Rat} :
    ratLt ratZero c -> ratLe (ratMul c a) (ratMul c b) -> ratLe a b := by
  intro hc h
  have swapped :
      ratLe (ratMul a c) (ratMul b c) :=
    ratLe_respects (ratMul_comm c a) (ratMul_comm c b) h
  exact ratMul_le_cancel_right hc swapped

private theorem ratLe_of_mul_left_nonneg_pos {c x : Rat} :
    ratLt ratZero c -> ratLe ratZero (ratMul c x) -> ratLe ratZero x := by
  intro hc h
  have shifted :
      ratLe (ratMul c ratZero) (ratMul c x) :=
    BEDC.Real.RatNumKernel.ratLe_of_RatEq_left
      (ratMul_zero_right_local c) h
  exact ratMul_le_cancel_left_pos hc shifted

private theorem ratAdd_sub_cancel_left_local (x y : Rat) :
    RatEq (ratAdd y (ratSub x y)) x := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (RatEq_symm
      (BEDC.Derived.LocatedReal.ratAdd_assoc_local y x (ratNeg y)))
    (RatEq_trans _ _ _
      (ratAdd_respects (ratAdd_comm y x) (RatEq_refl (ratNeg y)))
      (RatEq_trans _ _ _
        (BEDC.Derived.LocatedReal.ratAdd_assoc_local x y (ratNeg y))
        (RatEq_trans _ _ _
          (ratAdd_respects (RatEq_refl x)
            (BEDC.Derived.LocatedReal.ratAdd_neg_local y))
          (ratAdd_zero_right x))))

private theorem ratLe_of_sub_nonneg_local {x y : Rat} :
    ratLe ratZero (ratSub x y) -> ratLe y x := by
  intro h
  have raw :
      ratLe (ratAdd y ratZero) (ratAdd y (ratSub x y)) :=
    BEDC.Derived.LocatedReal.ratLe_add_left_mono
      (y := ratZero) (y' := ratSub x y) (x := y) h
  exact ratLe_respects
    (ratAdd_zero_right y)
    (ratAdd_sub_cancel_left_local x y)
    raw

theorem cube_nonneg_forces_base_nonneg (x : Rat)
    (h : ratLe ratZero (ratCube x)) :
    ratLe ratZero x := by
  cases rat_order_trichotomy ratZero x with
  | inl xPos =>
      exact ratLt_to_ratLe xPos
  | inr rest =>
      cases rest with
      | inl xZero =>
          exact ratLe_of_RatEq xZero
      | inr xNeg =>
          have negPos : ratLt ratZero (ratNeg x) :=
            ratNeg_pos_of_neg xNeg
          have negSqRaw :
              ratLt (ratMul ratZero (ratNeg x))
                (ratMul (ratNeg x) (ratNeg x)) :=
            ratMul_lt_mul_right negPos negPos
          have negSqPos :
              ratLt ratZero (ratMul (ratNeg x) (ratNeg x)) :=
            BEDC.Real.RatNumKernel.ratLt_of_RatEq_left
              (RatEq_symm (ratMul_zero_left_local (ratNeg x))) negSqRaw
          have xSqPos : ratLt ratZero (ratMul x x) :=
            BEDC.Real.RatNumKernel.ratLt_of_RatEq_right
              negSqPos (ratRing.neg_neg_mul_neg x x)
          have cubeNegRaw :
              ratLt (ratMul x (ratMul x x))
                (ratMul ratZero (ratMul x x)) :=
            ratMul_lt_mul_right xNeg xSqPos
          have cubeNeg : ratLt (ratCube x) ratZero := by
            change ratLt (ratMul x (ratMul x x)) ratZero
            exact BEDC.Real.RatNumKernel.ratLt_of_RatEq_right
              cubeNegRaw (ratMul_zero_left_local (ratMul x x))
          exact False.elim (ratLt_not_ratLe_reverse cubeNeg h)

theorem T3_nonneg_forces_A_nonneg (g0 g1 g2 g3 : Rat)
    (hT : ratLe ratZero (turanT3 g0 g1 g2 g3)) :
    ratLe ratZero (turanA g0 g1 g2 g3) := by
  let A := turanA g0 g1 g2 g3
  let HA := subdiscHA g0 g1 g2 g3
  let T := turanT3 g0 g1 g2 g3
  have hHA : ratLe ratZero (ratMul HA HA) :=
    ratMul_self_nonneg HA
  have hg0 : ratLe ratZero (ratMul g0 g0) :=
    ratMul_self_nonneg g0
  have hg0T : ratLe ratZero (ratMul (ratMul g0 g0) T) :=
    BEDC.Real.RatNumKernel.ratMul_nonneg hg0 hT
  have rhsNonneg :
      ratLe ratZero
        (ratAdd (ratMul HA HA) (ratMul (ratMul g0 g0) T)) :=
    ratAdd_nonneg_local hHA hg0T
  have ident := subdiscriminant_A g0 g1 g2 g3
  have lhsNonneg :
      ratLe ratZero (ratMul (natRat 4) (ratCube A)) :=
    BEDC.Real.RatNumKernel.ratLe_of_RatEq_right
      rhsNonneg (RatEq_symm ident)
  have cubeNonneg : ratLe ratZero (ratCube A) :=
    ratLe_of_mul_left_nonneg_pos natRat_four_pos lhsNonneg
  exact cube_nonneg_forces_base_nonneg A cubeNonneg

theorem T3_nonneg_forces_B_nonneg (g0 g1 g2 g3 : Rat)
    (hT : ratLe ratZero (turanT3 g0 g1 g2 g3)) :
    ratLe ratZero (turanB g0 g1 g2 g3) := by
  let B := turanB g0 g1 g2 g3
  let HB := subdiscHB g0 g1 g2 g3
  let T := turanT3 g0 g1 g2 g3
  have hHB : ratLe ratZero (ratMul HB HB) :=
    ratMul_self_nonneg HB
  have hg3 : ratLe ratZero (ratMul g3 g3) :=
    ratMul_self_nonneg g3
  have hg3T : ratLe ratZero (ratMul (ratMul g3 g3) T) :=
    BEDC.Real.RatNumKernel.ratMul_nonneg hg3 hT
  have rhsNonneg :
      ratLe ratZero
        (ratAdd (ratMul HB HB) (ratMul (ratMul g3 g3) T)) :=
    ratAdd_nonneg_local hHB hg3T
  have ident := subdiscriminant_B g0 g1 g2 g3
  have lhsNonneg :
      ratLe ratZero (ratMul (natRat 4) (ratCube B)) :=
    BEDC.Real.RatNumKernel.ratLe_of_RatEq_right
      rhsNonneg (RatEq_symm ident)
  have cubeNonneg : ratLe ratZero (ratCube B) :=
    ratLe_of_mul_left_nonneg_pos natRat_four_pos lhsNonneg
  exact cube_nonneg_forces_base_nonneg B cubeNonneg

theorem T3_nonneg_iff (g0 g1 g2 g3 : Rat) :
    ratLe ratZero (turanT3 g0 g1 g2 g3) ↔
      (ratLe ratZero (turanA g0 g1 g2 g3) ∧
        ratLe ratZero (turanB g0 g1 g2 g3) ∧
          ratLe
            (ratMul (turanC g0 g1 g2 g3) (turanC g0 g1 g2 g3))
            (ratMul (natRat 4)
              (ratMul (turanA g0 g1 g2 g3)
                (turanB g0 g1 g2 g3)))) := by
  constructor
  · intro hT
    have hA := T3_nonneg_forces_A_nonneg g0 g1 g2 g3 hT
    have hB := T3_nonneg_forces_B_nonneg g0 g1 g2 g3 hT
    have hC :
        ratLe
          (ratMul (turanC g0 g1 g2 g3) (turanC g0 g1 g2 g3))
          (ratMul (natRat 4)
            (ratMul (turanA g0 g1 g2 g3)
              (turanB g0 g1 g2 g3))) := by
      unfold turanT3 at hT
      exact ratLe_of_sub_nonneg_local hT
    exact ⟨hA, hB, hC⟩
  · intro h
    have hC := h.right.right
    unfold turanT3
    exact ratSub_nonneg_of_le hC

example :
    RatEq
      (turanT3 (natRat 18) (natRat 11) (natRat 6) (natRat 3))
      (natRat 12) := by
  exact RatEq_refl _

example :
    ratLe ratZero
      (turanT3 (natRat 18) (natRat 11) (natRat 6) (natRat 3)) := by
  have hT :
      RatEq
        (turanT3 (natRat 18) (natRat 11) (natRat 6) (natRat 3))
        (natRat 12) :=
    RatEq_refl _
  have h12 : ratLe ratZero (natRat 12) :=
    BEDC.Real.RatNumLogEnclosure.ratLeBool_true_to_ratLe (by rfl)
  exact BEDC.Real.RatNumKernel.ratLe_of_RatEq_right
    h12 (RatEq_symm hT)

example :
    RatEq
      (cubicDiscriminant (natRat 18) (natRat 11) (natRat 6) (natRat 3))
      (natRat 324) := by
  have hT :
      RatEq
        (turanT3 (natRat 18) (natRat 11) (natRat 6) (natRat 3))
        (natRat 12) :=
    RatEq_refl _
  have hDelta :=
    cubic_discriminant_eq_27_T3
      (natRat 18) (natRat 11) (natRat 6) (natRat 3)
  have hProd :
      RatEq
        (ratMul (natRat 27)
          (turanT3 (natRat 18) (natRat 11) (natRat 6) (natRat 3)))
        (ratMul (natRat 27) (natRat 12)) :=
    ratMul_respects (RatEq_refl _) hT
  have h324 :
      RatEq (ratMul (natRat 27) (natRat 12)) (natRat 324) :=
    RatEq_refl _
  exact RatEq_trans _ _ _ hDelta
    (RatEq_trans _ _ _ hProd h324)

end BEDC.Derived.RHRoute.JensenTuranDegree3
