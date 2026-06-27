import BEDC.Algebra.FiniteFold
import BEDC.Derived.QuaternionUp

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

namespace BEDC.Derived.OctonionUp

abbrev Z := BEDC.Derived.QuaternionUp.IntegerUp
abbrev Zeq := BEDC.Derived.QuaternionUp.IntEq
abbrev Zzero := BEDC.Derived.QuaternionUp.intZero
abbrev Zone := BEDC.Derived.QuaternionUp.intOne
abbrev Zadd := BEDC.Derived.QuaternionUp.IntAdd
abbrev Zmul := BEDC.Derived.QuaternionUp.IntMul
abbrev Zneg := BEDC.Derived.QuaternionUp.IntNeg


abbrev Quat := BEDC.Derived.QuaternionUp.Quat
abbrev QuatEq := BEDC.Derived.QuaternionUp.QuatEq
abbrev quatZero := BEDC.Derived.QuaternionUp.quatZero
abbrev quatOne := BEDC.Derived.QuaternionUp.quatOne
abbrev quatAdd := BEDC.Derived.QuaternionUp.quatAdd
abbrev quatNeg := BEDC.Derived.QuaternionUp.quatNeg
abbrev quatSub := fun x y : Quat => quatAdd x (quatNeg y)
abbrev quatMul := BEDC.Derived.QuaternionUp.quatMul
abbrev quatConj := BEDC.Derived.QuaternionUp.quatConj
abbrev quatNorm := BEDC.Derived.QuaternionUp.quatNorm

infix:50 " ≈q " => QuatEq

structure Oct where
  fst : Quat
  snd : Quat

def octEq (x y : Oct) : Prop :=
  x.fst ≈q y.fst ∧ x.snd ≈q y.snd

def octZero : Oct :=
  { fst := quatZero, snd := quatZero }

def octOne : Oct :=
  { fst := quatOne, snd := quatZero }

def octAdd (x y : Oct) : Oct :=
  { fst := quatAdd x.fst y.fst
    snd := quatAdd x.snd y.snd }

def octNeg (x : Oct) : Oct :=
  { fst := quatNeg x.fst
    snd := quatNeg x.snd }

def octConj (x : Oct) : Oct :=
  { fst := quatConj x.fst
    snd := quatNeg x.snd }

def octMul (x y : Oct) : Oct :=
  { fst := quatSub (quatMul x.fst y.fst) (quatMul (quatConj y.snd) x.snd)
    snd := quatAdd (quatMul y.snd x.fst) (quatMul x.snd (quatConj y.fst)) }

def octNorm (x : Oct) : Z :=
  Zadd (quatNorm x.fst) (quatNorm x.snd)

private def zring : BEDC.Algebra.Rel.RelCommRing Z Zeq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

private theorem zEq_refl (x : Z) : x ≈z x :=
  zring.refl x

private theorem zEq_symm {x y : Z} : x ≈z y -> y ≈z x :=
  zring.symm

private theorem zEq_trans {x y z : Z} : x ≈z y -> y ≈z z -> x ≈z z :=
  zring.trans

private theorem zAdd_respects {a a' b b' : Z} :
    a ≈z a' -> b ≈z b' -> Zadd a b ≈z Zadd a' b' :=
  zring.add_congr

private theorem zMul_respects {a a' b b' : Z} :
    a ≈z a' -> b ≈z b' -> Zmul a b ≈z Zmul a' b' :=
  zring.mul_congr

private theorem zNeg_respects {a b : Z} :
    a ≈z b -> Zneg a ≈z Zneg b :=
  zring.neg_congr

private theorem zAdd_zero (a : Z) : Zadd a Zzero ≈z a :=
  zring.add_zero a

private theorem zZero_add (a : Z) : Zadd Zzero a ≈z a :=
  zring.zero_add a

private theorem zAdd_neg (a : Z) : Zadd a (Zneg a) ≈z Zzero :=
  zring.add_neg a

private theorem zNeg_add (a : Z) : Zadd (Zneg a) a ≈z Zzero :=
  zring.neg_add a

private theorem zMul_one (a : Z) : Zmul a Zone ≈z a :=
  zring.mul_one a

private theorem zOne_mul (a : Z) : Zmul Zone a ≈z a :=
  zring.one_mul a

private theorem zMul_zero (a : Z) : Zmul a Zzero ≈z Zzero :=
  zring.mul_zero a

private theorem zZero_mul (a : Z) : Zmul Zzero a ≈z Zzero :=
  zring.zero_mul a

private theorem zNeg_neg (a : Z) : Zneg (Zneg a) ≈z a :=
  zring.neg_neg a

private theorem zSub_respects {a a' b b' : Z} :
    a ≈z a' -> b ≈z b' -> Zadd a (Zneg b) ≈z Zadd a' (Zneg b') := by
  intro ha hb
  exact zring.add_congr ha (zring.neg_congr hb)

private theorem zNeg_zero : Zneg Zzero ≈z Zzero :=
  zring.neg_zero

private theorem zSub_zero (a : Z) : Zadd a (Zneg Zzero) ≈z a := by
  exact zring.trans (zring.add_congr (zEq_refl a) zNeg_zero) (zring.add_zero a)

private theorem zZero_sub (a : Z) : Zadd Zzero (Zneg a) ≈z Zneg a :=
  zring.zero_add (Zneg a)

private theorem zSub_self (a : Z) : Zadd a (Zneg a) ≈z Zzero :=
  zring.add_neg a

private theorem qEq_refl (x : Quat) : x ≈q x :=
  BEDC.Derived.QuaternionUp.QuatEq_refl x

private theorem qEq_symm {x y : Quat} : x ≈q y -> y ≈q x :=
  BEDC.Derived.QuaternionUp.QuatEq_symm

private theorem qEq_trans {x y z : Quat} : x ≈q y -> y ≈q z -> x ≈q z :=
  BEDC.Derived.QuaternionUp.QuatEq_trans

instance quatEqTrans : Trans QuatEq QuatEq QuatEq where
  trans := by
    intro _ _ _
    exact qEq_trans

private theorem qAdd_respects {a a' b b' : Quat} :
    a ≈q a' -> b ≈q b' -> quatAdd a b ≈q quatAdd a' b' :=
  BEDC.Derived.QuaternionUp.quatAdd_respects

private theorem qNeg_respects {a b : Quat} :
    a ≈q b -> quatNeg a ≈q quatNeg b :=
  BEDC.Derived.QuaternionUp.quatNeg_respects

private theorem qMul_respects {a a' b b' : Quat} :
    a ≈q a' -> b ≈q b' -> quatMul a b ≈q quatMul a' b' :=
  BEDC.Derived.QuaternionUp.quatMul_respects

private theorem qConj_respects {a b : Quat} :
    a ≈q b -> quatConj a ≈q quatConj b :=
  BEDC.Derived.QuaternionUp.quatConj_respects

private theorem qAdd_comm (a b : Quat) :
    quatAdd a b ≈q quatAdd b a :=
  BEDC.Derived.QuaternionUp.quatAdd_comm a b

private theorem qAdd_assoc (a b c : Quat) :
    quatAdd (quatAdd a b) c ≈q quatAdd a (quatAdd b c) :=
  BEDC.Derived.QuaternionUp.quatAdd_assoc a b c

private theorem qAdd_zero (a : Quat) :
    quatAdd a quatZero ≈q a :=
  BEDC.Derived.QuaternionUp.quatAdd_zero a

private theorem qZero_add (a : Quat) :
    quatAdd quatZero a ≈q a :=
  BEDC.Derived.QuaternionUp.quatZero_add a

private theorem qAdd_neg (a : Quat) :
    quatAdd a (quatNeg a) ≈q quatZero :=
  BEDC.Derived.QuaternionUp.quatAdd_neg a

private theorem qNeg_add (a : Quat) :
    quatAdd (quatNeg a) a ≈q quatZero :=
  BEDC.Derived.QuaternionUp.quatNeg_add a

private theorem qMul_one (a : Quat) :
    quatMul a quatOne ≈q a :=
  BEDC.Derived.QuaternionUp.quatMul_one a

private theorem qOne_mul (a : Quat) :
    quatMul quatOne a ≈q a :=
  BEDC.Derived.QuaternionUp.quatOne_mul a

private theorem qMul_zero (a : Quat) :
    quatMul a quatZero ≈q quatZero :=
  BEDC.Derived.QuaternionUp.quatMul_zero a

private theorem qZero_mul (a : Quat) :
    quatMul quatZero a ≈q quatZero :=
  BEDC.Derived.QuaternionUp.quatZero_mul a

private theorem qMul_assoc (a b c : Quat) :
    quatMul (quatMul a b) c ≈q quatMul a (quatMul b c) :=
  BEDC.Derived.QuaternionUp.quatMul_assoc a b c

private theorem qMul_add_distrib (a b c : Quat) :
    quatMul a (quatAdd b c) ≈q quatAdd (quatMul a b) (quatMul a c) :=
  BEDC.Derived.QuaternionUp.quatMul_add_distrib a b c

private theorem qAdd_mul_distrib (a b c : Quat) :
    quatMul (quatAdd a b) c ≈q quatAdd (quatMul a c) (quatMul b c) :=
  BEDC.Derived.QuaternionUp.quatAdd_mul_distrib a b c

private theorem qNorm_respects {a b : Quat} :
    a ≈q b -> quatNorm a ≈z quatNorm b :=
  BEDC.Derived.QuaternionUp.quatNorm_respects

private theorem qNeg_zero : quatNeg quatZero ≈q quatZero := by
  exact ⟨zNeg_zero, zNeg_zero, zNeg_zero, zNeg_zero⟩

private theorem qConj_one : quatConj quatOne ≈q quatOne := by
  change QuatEq
    { re := Zone, imI := Zneg Zzero, imJ := Zneg Zzero, imK := Zneg Zzero }
    { re := Zone, imI := Zzero, imJ := Zzero, imK := Zzero }
  exact ⟨zEq_refl Zone, zNeg_zero, zNeg_zero, zNeg_zero⟩

private theorem qNeg_neg (a : Quat) : quatNeg (quatNeg a) ≈q a := by
  exact ⟨zNeg_neg a.re, zNeg_neg a.imI, zNeg_neg a.imJ, zNeg_neg a.imK⟩

private theorem qSub_respects {a a' b b' : Quat} :
    a ≈q a' -> b ≈q b' -> quatSub a b ≈q quatSub a' b' := by
  intro ha hb
  exact qAdd_respects ha (qNeg_respects hb)

private theorem qSub_zero (a : Quat) : quatSub a quatZero ≈q a := by
  exact qEq_trans (qAdd_respects (qEq_refl a) qNeg_zero) (qAdd_zero a)

private theorem qZero_sub (a : Quat) : quatSub quatZero a ≈q quatNeg a :=
  qZero_add (quatNeg a)

private theorem qSub_self (a : Quat) : quatSub a a ≈q quatZero :=
  qAdd_neg a

theorem octEq_refl (x : Oct) : octEq x x :=
  ⟨qEq_refl x.fst, qEq_refl x.snd⟩

theorem octEq_symm {x y : Oct} : octEq x y -> octEq y x := by
  intro h
  exact ⟨qEq_symm h.left, qEq_symm h.right⟩

theorem octEq_trans {x y z : Oct} :
    octEq x y -> octEq y z -> octEq x z := by
  intro hxy hyz
  exact ⟨qEq_trans hxy.left hyz.left, qEq_trans hxy.right hyz.right⟩

theorem octAdd_respects {x x' y y' : Oct} :
    octEq x x' -> octEq y y' -> octEq (octAdd x y) (octAdd x' y') := by
  intro hx hy
  exact ⟨qAdd_respects hx.left hy.left, qAdd_respects hx.right hy.right⟩

theorem octNeg_respects {x y : Oct} :
    octEq x y -> octEq (octNeg x) (octNeg y) := by
  intro h
  exact ⟨qNeg_respects h.left, qNeg_respects h.right⟩

theorem octConj_respects {x y : Oct} :
    octEq x y -> octEq (octConj x) (octConj y) := by
  intro h
  exact ⟨qConj_respects h.left, qNeg_respects h.right⟩

theorem octMul_respects {x x' y y' : Oct} :
    octEq x x' -> octEq y y' -> octEq (octMul x y) (octMul x' y') := by
  intro hx hy
  exact
    ⟨qSub_respects
        (qMul_respects hx.left hy.left)
        (qMul_respects (qConj_respects hy.right) hx.right),
      qAdd_respects
        (qMul_respects hy.right hx.left)
        (qMul_respects hx.right (qConj_respects hy.left))⟩

theorem octAdd_comm (x y : Oct) : octEq (octAdd x y) (octAdd y x) := by
  exact ⟨qAdd_comm x.fst y.fst, qAdd_comm x.snd y.snd⟩

theorem octAdd_assoc (x y z : Oct) :
    octEq (octAdd (octAdd x y) z) (octAdd x (octAdd y z)) := by
  exact ⟨qAdd_assoc x.fst y.fst z.fst, qAdd_assoc x.snd y.snd z.snd⟩

theorem octAdd_zero (x : Oct) : octEq (octAdd x octZero) x := by
  exact ⟨qAdd_zero x.fst, qAdd_zero x.snd⟩

theorem octZero_add (x : Oct) : octEq (octAdd octZero x) x := by
  exact ⟨qZero_add x.fst, qZero_add x.snd⟩

theorem octAdd_neg (x : Oct) : octEq (octAdd x (octNeg x)) octZero := by
  exact ⟨qAdd_neg x.fst, qAdd_neg x.snd⟩

theorem octNeg_add (x : Oct) : octEq (octAdd (octNeg x) x) octZero := by
  exact ⟨qNeg_add x.fst, qNeg_add x.snd⟩

theorem octConj_conj (x : Oct) : octEq (octConj (octConj x)) x := by
  exact
    ⟨by
        exact ⟨zEq_refl x.fst.re, zNeg_neg x.fst.imI,
          zNeg_neg x.fst.imJ, zNeg_neg x.fst.imK⟩,
      qNeg_neg x.snd⟩

theorem octMul_one (x : Oct) : octEq (octMul x octOne) x := by
  constructor
  · calc
      quatSub (quatMul x.fst quatOne) (quatMul (quatConj quatZero) x.snd)
          ≈q quatSub x.fst quatZero :=
            qSub_respects (qMul_one x.fst)
              (qEq_trans (qMul_respects qNeg_zero (qEq_refl x.snd)) (qZero_mul x.snd))
      _ ≈q x.fst := qSub_zero x.fst
  · calc
      quatAdd (quatMul quatZero x.fst) (quatMul x.snd (quatConj quatOne))
          ≈q quatAdd quatZero x.snd :=
            qAdd_respects (qZero_mul x.fst)
              (qEq_trans
                (qMul_respects (qEq_refl x.snd) qConj_one)
                (qMul_one x.snd))
      _ ≈q x.snd := qZero_add x.snd

theorem octOne_mul (x : Oct) : octEq (octMul octOne x) x := by
  constructor
  · calc
      quatSub (quatMul quatOne x.fst) (quatMul (quatConj x.snd) quatZero)
          ≈q quatSub x.fst quatZero :=
            qSub_respects (qOne_mul x.fst) (qMul_zero (quatConj x.snd))
      _ ≈q x.fst := qSub_zero x.fst
  · calc
      quatAdd (quatMul x.snd quatOne) (quatMul quatZero (quatConj x.fst))
          ≈q quatAdd x.snd quatZero :=
            qAdd_respects (qMul_one x.snd) (qZero_mul (quatConj x.fst))
      _ ≈q x.snd := qAdd_zero x.snd

theorem octMul_zero (x : Oct) : octEq (octMul x octZero) octZero := by
  constructor
  · calc
      quatSub (quatMul x.fst quatZero) (quatMul (quatConj quatZero) x.snd)
          ≈q quatSub quatZero quatZero :=
            qSub_respects (qMul_zero x.fst)
              (qEq_trans (qMul_respects qNeg_zero (qEq_refl x.snd)) (qZero_mul x.snd))
      _ ≈q quatZero := qSub_self quatZero
  · calc
      quatAdd (quatMul quatZero x.fst) (quatMul x.snd (quatConj quatZero))
          ≈q quatAdd quatZero quatZero :=
            qAdd_respects (qZero_mul x.fst)
              (qEq_trans (qMul_respects (qEq_refl x.snd) qNeg_zero) (qMul_zero x.snd))
      _ ≈q quatZero := qZero_add quatZero

theorem octZero_mul (x : Oct) : octEq (octMul octZero x) octZero := by
  constructor
  · calc
      quatSub (quatMul quatZero x.fst) (quatMul (quatConj x.snd) quatZero)
          ≈q quatSub quatZero quatZero :=
            qSub_respects (qZero_mul x.fst) (qMul_zero (quatConj x.snd))
      _ ≈q quatZero := qSub_self quatZero
  · calc
      quatAdd (quatMul x.snd quatZero) (quatMul quatZero (quatConj x.fst))
          ≈q quatAdd quatZero quatZero :=
            qAdd_respects (qMul_zero x.snd) (qZero_mul (quatConj x.fst))
      _ ≈q quatZero := qZero_add quatZero

theorem octNorm_respects {x y : Oct} :
    octEq x y -> octNorm x ≈z octNorm y := by
  intro h
  exact zAdd_respects (qNorm_respects h.left) (qNorm_respects h.right)

private theorem zNeg_add_pair (a b : Z) :
    Zneg (Zadd a b) ≈z Zadd (Zneg a) (Zneg b) := by
  have hzero :
      Zadd (Zadd a b) (Zadd (Zneg a) (Zneg b)) ≈z Zzero := by
    calc
      Zadd (Zadd a b) (Zadd (Zneg a) (Zneg b))
          ≈z Zadd (Zadd a (Zneg a)) (Zadd b (Zneg b)) :=
            zring.trans (zring.add_assoc a b (Zadd (Zneg a) (Zneg b)))
              (zring.trans
                (zring.add_congr (zEq_refl a)
                  (zring.symm (zring.add_assoc b (Zneg a) (Zneg b))))
                (zring.trans
                  (zring.add_congr (zEq_refl a)
                    (zring.add_congr (zring.add_comm b (Zneg a))
                      (zEq_refl (Zneg b))))
                  (zring.trans
                    (zring.add_congr (zEq_refl a)
                      (zring.add_assoc (Zneg a) b (Zneg b)))
                    (zring.symm (zring.add_assoc a (Zneg a)
                      (Zadd b (Zneg b)))))))
      _ ≈z Zadd Zzero Zzero :=
            zring.add_congr (zAdd_neg a) (zAdd_neg b)
      _ ≈z Zzero := zZero_add Zzero
  exact zring.symm
    (zring.eq_neg_of_add_eq_zero (a := Zadd a b)
      (b := Zadd (Zneg a) (Zneg b)) hzero)

private inductive ZExpr where
  | var : Nat -> ZExpr
  | add : ZExpr -> ZExpr -> ZExpr
  | mul : ZExpr -> ZExpr -> ZExpr
  | neg : ZExpr -> ZExpr

private structure ZTerm where
  neg : Bool
  vars : List Nat

private def eSub (a b : ZExpr) : ZExpr :=
  ZExpr.add a (ZExpr.neg b)

private def zMonoEval (vars : Nat -> Z) : List Nat -> Z
  | [] => Zone
  | i :: rest => Zmul (vars i) (zMonoEval vars rest)

private def zTermEval (vars : Nat -> Z) (t : ZTerm) : Z :=
  if t.neg then Zneg (zMonoEval vars t.vars) else zMonoEval vars t.vars

private def zExprEval (vars : Nat -> Z) : ZExpr -> Z
  | ZExpr.var i => vars i
  | ZExpr.add a b => Zadd (zExprEval vars a) (zExprEval vars b)
  | ZExpr.mul a b => Zmul (zExprEval vars a) (zExprEval vars b)
  | ZExpr.neg a => Zneg (zExprEval vars a)

private def zTermNeg (t : ZTerm) : ZTerm :=
  { neg := !t.neg, vars := t.vars }

private def zTermMul (t u : ZTerm) : ZTerm :=
  { neg := if t.neg then !u.neg else u.neg, vars := t.vars ++ u.vars }

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

private def natListLeBool (a b : Nat) : Bool :=
  natLeBool a b

private def natInsert (x : Nat) : List Nat -> List Nat
  | [] => [x]
  | y :: ys => if natListLeBool x y then x :: y :: ys else y :: natInsert x ys

private def natSort : List Nat -> List Nat
  | [] => []
  | x :: xs => natInsert x (natSort xs)

private def zTermCanonical (t : ZTerm) : ZTerm :=
  { neg := t.neg, vars := natSort t.vars }

private def zTermsMulOne (t : ZTerm) : List ZTerm -> List ZTerm
  | [] => []
  | u :: us => zTermMul t u :: zTermsMulOne t us

private def zTermsMul : List ZTerm -> List ZTerm -> List ZTerm
  | [], _ => []
  | t :: ts, us => zTermsMulOne t us ++ zTermsMul ts us

private def zExprTerms : ZExpr -> List ZTerm
  | ZExpr.var i => [{ neg := false, vars := [i] }]
  | ZExpr.add a b => zExprTerms a ++ zExprTerms b
  | ZExpr.mul a b => zTermsMul (zExprTerms a) (zExprTerms b)
  | ZExpr.neg a => List.map zTermNeg (zExprTerms a)

private def natLexLeBool : List Nat -> List Nat -> Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
      if natEqBool a b then natLexLeBool as bs else natLeBool a b

private def zTermLeBool (a b : ZTerm) : Bool :=
  if natListEqBool a.vars b.vars then
    match a.neg, b.neg with
    | false, false => true
    | false, true => true
    | true, false => false
    | true, true => true
  else
    natLexLeBool a.vars b.vars

private def zTermInsert (t : ZTerm) : List ZTerm -> List ZTerm
  | [] => [t]
  | u :: us =>
      if zTermLeBool t u then t :: u :: us else u :: zTermInsert t us

private def zTermSort : List ZTerm -> List ZTerm
  | [] => []
  | t :: ts => zTermInsert t (zTermSort ts)

private def zTermOppositeSame (a b : ZTerm) : Bool :=
  match a.neg, b.neg with
  | false, false => false
  | false, true => natListEqBool a.vars b.vars
  | true, false => natListEqBool a.vars b.vars
  | true, true => false

private def zCancelStep : List ZTerm -> ZTerm -> List ZTerm
  | [], t => [t]
  | u :: us, t =>
      if zTermOppositeSame t u then us else t :: u :: us

private def zCancelGo : List ZTerm -> List ZTerm -> List ZTerm
  | acc, [] => acc
  | acc, t :: ts => zCancelGo (zCancelStep acc t) ts

private def zCancelTerms (terms : List ZTerm) : List ZTerm :=
  zTermSort (zCancelGo [] terms)

private def zExprNorm (e : ZExpr) : List ZTerm :=
  zCancelTerms (zTermSort (List.map zTermCanonical (zExprTerms e)))

private def zSumTerms (vars : Nat -> Z) : List ZTerm -> Z
  | [] => Zzero
  | t :: terms => Zadd (zTermEval vars t) (zSumTerms vars terms)

private theorem natInsert_perm (x : Nat) :
    ∀ xs : List Nat,
      BEDC.Algebra.FiniteFold.ListPerm (natInsert x xs) (x :: xs)
  | [] => by
      exact BEDC.Algebra.FiniteFold.ListPerm.cons x
        BEDC.Algebra.FiniteFold.ListPerm.nil
  | y :: ys => by
      cases h : natListLeBool x y
      · unfold natInsert
        rw [h]
        exact BEDC.Algebra.FiniteFold.ListPerm.trans
          (BEDC.Algebra.FiniteFold.ListPerm.cons y (natInsert_perm x ys))
          (BEDC.Algebra.FiniteFold.ListPerm.swap y x ys)
      · unfold natInsert
        rw [h]
        exact BEDC.Algebra.FiniteFold.listPerm_refl (x :: y :: ys)

private theorem natSort_perm :
    ∀ xs : List Nat,
      BEDC.Algebra.FiniteFold.ListPerm (natSort xs) xs
  | [] => BEDC.Algebra.FiniteFold.ListPerm.nil
  | x :: xs =>
      BEDC.Algebra.FiniteFold.ListPerm.trans
        (natInsert_perm x (natSort xs))
        (BEDC.Algebra.FiniteFold.ListPerm.cons x (natSort_perm xs))

private theorem zMonoEval_perm (vars : Nat -> Z) :
    ∀ {xs ys : List Nat},
      BEDC.Algebra.FiniteFold.ListPerm xs ys ->
        zMonoEval vars xs ≈z zMonoEval vars ys
  | _, _, BEDC.Algebra.FiniteFold.ListPerm.nil =>
      zEq_refl Zone
  | _, _, BEDC.Algebra.FiniteFold.ListPerm.cons x p => by
      exact zring.mul_congr (zEq_refl (vars x)) (zMonoEval_perm vars p)
  | _, _, BEDC.Algebra.FiniteFold.ListPerm.swap x y xs => by
      exact zring.trans (zring.symm (zring.mul_assoc (vars x) (vars y) (zMonoEval vars xs)))
        (zring.trans
          (zring.mul_congr (zring.mul_comm (vars x) (vars y))
            (zEq_refl (zMonoEval vars xs)))
          (zring.mul_assoc (vars y) (vars x) (zMonoEval vars xs)))
  | _, _, BEDC.Algebra.FiniteFold.ListPerm.trans p q =>
      zring.trans (zMonoEval_perm vars p) (zMonoEval_perm vars q)

private theorem zTermCanonical_eval (vars : Nat -> Z) (t : ZTerm) :
    zTermEval vars (zTermCanonical t) ≈z zTermEval vars t := by
  cases t with
  | mk isNeg mono =>
      cases isNeg
      · exact zMonoEval_perm vars (natSort_perm mono)
      · exact zring.neg_congr (zMonoEval_perm vars (natSort_perm mono))

private theorem zSum_canonical (vars : Nat -> Z) :
    ∀ terms : List ZTerm,
      zSumTerms vars (List.map zTermCanonical terms) ≈z zSumTerms vars terms
  | [] => zEq_refl Zzero
  | t :: ts => by
      exact zring.add_congr (zTermCanonical_eval vars t) (zSum_canonical vars ts)

private theorem zTermInsert_perm (t : ZTerm) :
    ∀ terms : List ZTerm,
      BEDC.Algebra.FiniteFold.ListPerm (zTermInsert t terms) (t :: terms)
  | [] => by
      exact BEDC.Algebra.FiniteFold.ListPerm.cons t
        BEDC.Algebra.FiniteFold.ListPerm.nil
  | u :: us => by
      cases h : zTermLeBool t u
      · unfold zTermInsert
        rw [h]
        exact BEDC.Algebra.FiniteFold.ListPerm.trans
          (BEDC.Algebra.FiniteFold.ListPerm.cons u (zTermInsert_perm t us))
          (BEDC.Algebra.FiniteFold.ListPerm.swap u t us)
      · unfold zTermInsert
        rw [h]
        exact BEDC.Algebra.FiniteFold.listPerm_refl (t :: u :: us)

private theorem zTermSort_perm :
    ∀ terms : List ZTerm,
      BEDC.Algebra.FiniteFold.ListPerm (zTermSort terms) terms
  | [] => BEDC.Algebra.FiniteFold.ListPerm.nil
  | t :: ts =>
      BEDC.Algebra.FiniteFold.ListPerm.trans
        (zTermInsert_perm t (zTermSort ts))
        (BEDC.Algebra.FiniteFold.ListPerm.cons t (zTermSort_perm ts))

private theorem zSum_perm (vars : Nat -> Z) :
    ∀ {xs ys : List ZTerm},
      BEDC.Algebra.FiniteFold.ListPerm xs ys ->
        zSumTerms vars xs ≈z zSumTerms vars ys
  | _, _, BEDC.Algebra.FiniteFold.ListPerm.nil =>
      zEq_refl Zzero
  | _, _, BEDC.Algebra.FiniteFold.ListPerm.cons x p => by
      exact zring.add_congr (zEq_refl (zTermEval vars x)) (zSum_perm vars p)
  | _, _, BEDC.Algebra.FiniteFold.ListPerm.swap x y xs => by
      exact zring.trans
        (zring.symm (zring.add_assoc (zTermEval vars x) (zTermEval vars y)
          (zSumTerms vars xs)))
        (zring.trans
          (zring.add_congr (zring.add_comm (zTermEval vars x) (zTermEval vars y))
            (zEq_refl (zSumTerms vars xs)))
          (zring.add_assoc (zTermEval vars y) (zTermEval vars x)
            (zSumTerms vars xs)))
  | _, _, BEDC.Algebra.FiniteFold.ListPerm.trans p q =>
      zring.trans (zSum_perm vars p) (zSum_perm vars q)

private theorem zSum_sort (vars : Nat -> Z) (terms : List ZTerm) :
    zSumTerms vars (zTermSort terms) ≈z zSumTerms vars terms := by
  exact zSum_perm vars (zTermSort_perm terms)

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

private theorem zTermOppositeSame_eval_zero
    (vars : Nat -> Z) (t u : ZTerm) :
    zTermOppositeSame t u = true ->
      Zadd (zTermEval vars t) (zTermEval vars u) ≈z Zzero := by
  intro h
  cases t with
  | mk tNeg tVars =>
      cases u with
      | mk uNeg uVars =>
          cases tNeg <;> cases uNeg
          · cases h
          · unfold zTermOppositeSame at h
            have sameVars := natListEqBool_eq_true tVars uVars h
            rw [sameVars]
            change Zadd (zMonoEval vars uVars) (Zneg (zMonoEval vars uVars)) ≈z Zzero
            exact zAdd_neg (zMonoEval vars uVars)
          · unfold zTermOppositeSame at h
            have sameVars := natListEqBool_eq_true tVars uVars h
            rw [sameVars]
            change Zadd (Zneg (zMonoEval vars uVars)) (zMonoEval vars uVars) ≈z Zzero
            exact zNeg_add (zMonoEval vars uVars)
          · cases h

private theorem zCancelStep_sound (vars : Nat -> Z) :
    ∀ acc : List ZTerm, ∀ t : ZTerm,
      zSumTerms vars (zCancelStep acc t) ≈z
        Zadd (zTermEval vars t) (zSumTerms vars acc)
  | [], t => by
      exact zring.refl (Zadd (zTermEval vars t) Zzero)
  | u :: us, t => by
      cases h : zTermOppositeSame t u
      · change zSumTerms vars
          (if zTermOppositeSame t u then us else t :: u :: us) ≈z
          Zadd (zTermEval vars t) (Zadd (zTermEval vars u) (zSumTerms vars us))
        rw [h]
        exact zring.refl (Zadd (zTermEval vars t) (Zadd (zTermEval vars u) (zSumTerms vars us)))
      · change zSumTerms vars
          (if zTermOppositeSame t u then us else t :: u :: us) ≈z
          Zadd (zTermEval vars t) (Zadd (zTermEval vars u) (zSumTerms vars us))
        rw [h]
        exact zring.symm
          (zring.trans
            (zring.symm (zring.add_assoc (zTermEval vars t)
              (zTermEval vars u) (zSumTerms vars us)))
            (zring.trans
              (zring.add_congr (zTermOppositeSame_eval_zero vars t u h)
                (zring.refl (zSumTerms vars us)))
              (zring.zero_add (zSumTerms vars us))))

private theorem zCancelGo_sound (vars : Nat -> Z) :
    ∀ acc terms : List ZTerm,
      zSumTerms vars (zCancelGo acc terms) ≈z
        Zadd (zSumTerms vars terms) (zSumTerms vars acc)
  | acc, [] => by
      exact zring.symm (zring.zero_add (zSumTerms vars acc))
  | acc, t :: ts => by
      have tail := zCancelGo_sound vars (zCancelStep acc t) ts
      exact zring.trans tail
        (zring.trans
          (zring.add_congr (zring.refl (zSumTerms vars ts))
            (zCancelStep_sound vars acc t))
          (zring.trans
            (zring.symm (zring.add_assoc (zSumTerms vars ts)
              (zTermEval vars t) (zSumTerms vars acc)))
            (zring.add_congr
              (zring.add_comm (zSumTerms vars ts) (zTermEval vars t))
              (zring.refl (zSumTerms vars acc)))))

private theorem zCancelTerms_sound (vars : Nat -> Z) (terms : List ZTerm) :
    zSumTerms vars (zCancelTerms terms) ≈z zSumTerms vars terms := by
  unfold zCancelTerms
  exact zring.trans (zSum_sort vars (zCancelGo [] terms))
    (zring.trans (zCancelGo_sound vars [] terms)
      (zring.trans
        (zring.add_congr (zring.refl (zSumTerms vars terms))
          (zring.refl Zzero))
        (zring.add_zero (zSumTerms vars terms))))

private theorem zSum_append (vars : Nat -> Z) (xs ys : List ZTerm) :
    zSumTerms vars (xs ++ ys) ≈z Zadd (zSumTerms vars xs) (zSumTerms vars ys) := by
  induction xs with
  | nil =>
      exact zring.symm (zring.zero_add (zSumTerms vars ys))
  | cons x xs ih =>
      exact zring.trans
        (zring.add_congr (zEq_refl (zTermEval vars x)) ih)
        (zring.symm (zring.add_assoc (zTermEval vars x)
          (zSumTerms vars xs) (zSumTerms vars ys)))

private theorem zMonoEval_append (vars : Nat -> Z) :
    ∀ xs ys : List Nat,
      zMonoEval vars (xs ++ ys) ≈z Zmul (zMonoEval vars xs) (zMonoEval vars ys)
  | [], ys => by
      exact zring.symm (zring.one_mul (zMonoEval vars ys))
  | x :: xs, ys => by
      exact zring.trans
        (zring.mul_congr (zEq_refl (vars x)) (zMonoEval_append vars xs ys))
        (zring.symm (zring.mul_assoc (vars x) (zMonoEval vars xs)
          (zMonoEval vars ys)))

private theorem zTermEval_neg (vars : Nat -> Z) (t : ZTerm) :
    zTermEval vars (zTermNeg t) ≈z Zneg (zTermEval vars t) := by
  cases t with
  | mk isNeg mono =>
      cases isNeg
      · exact zEq_refl (Zneg (zMonoEval vars mono))
      · exact zring.symm (zNeg_neg (zMonoEval vars mono))

private theorem zTermEval_mul (vars : Nat -> Z) (t u : ZTerm) :
    zTermEval vars (zTermMul t u) ≈z
      Zmul (zTermEval vars t) (zTermEval vars u) := by
  cases t with
  | mk tNeg tVars =>
      cases u with
      | mk uNeg uVars =>
          cases tNeg <;> cases uNeg
          · exact zMonoEval_append vars tVars uVars
          · exact zring.trans
              (zring.neg_congr (zMonoEval_append vars tVars uVars))
              (zring.symm (zring.mul_neg (zMonoEval vars tVars)
                (zMonoEval vars uVars)))
          · exact zring.trans
              (zring.neg_congr (zMonoEval_append vars tVars uVars))
              (zring.symm (zring.neg_mul (zMonoEval vars tVars)
                (zMonoEval vars uVars)))
          · exact zring.trans (zMonoEval_append vars tVars uVars)
              (zring.symm (zring.neg_neg_mul_neg (zMonoEval vars tVars)
                (zMonoEval vars uVars)))

private theorem zSum_neg (vars : Nat -> Z) :
    ∀ terms : List ZTerm,
      zSumTerms vars (List.map zTermNeg terms) ≈z Zneg (zSumTerms vars terms)
  | [] => by
      exact zring.symm zNeg_zero
  | t :: ts => by
      exact zring.trans
        (zring.add_congr (zTermEval_neg vars t) (zSum_neg vars ts))
        (zring.symm (zNeg_add_pair (zTermEval vars t) (zSumTerms vars ts)))

private theorem zTermsMulOne_sound (vars : Nat -> Z) (t : ZTerm) :
    ∀ terms : List ZTerm,
      zSumTerms vars (zTermsMulOne t terms) ≈z
        Zmul (zTermEval vars t) (zSumTerms vars terms)
  | [] => by
      exact zring.symm (zring.mul_zero (zTermEval vars t))
  | u :: us => by
      exact zring.trans
        (zring.add_congr (zTermEval_mul vars t u) (zTermsMulOne_sound vars t us))
        (zring.symm (zring.left_distrib (zTermEval vars t)
          (zTermEval vars u) (zSumTerms vars us)))

private theorem zTermsMul_sound (vars : Nat -> Z) :
    ∀ xs ys : List ZTerm,
      zSumTerms vars (zTermsMul xs ys) ≈z
        Zmul (zSumTerms vars xs) (zSumTerms vars ys)
  | [], ys => by
      exact zring.symm (zring.zero_mul (zSumTerms vars ys))
  | x :: xs, ys => by
      exact zring.trans
        (zSum_append vars (zTermsMulOne x ys) (zTermsMul xs ys))
        (zring.trans
          (zring.add_congr (zTermsMulOne_sound vars x ys)
            (zTermsMul_sound vars xs ys))
          (zring.symm (zring.right_distrib (zTermEval vars x)
            (zSumTerms vars xs) (zSumTerms vars ys))))

private theorem zExprTerms_sound_var (vars : Nat -> Z) (i : Nat) :
    zExprEval vars (ZExpr.var i) ≈z zSumTerms vars (zExprTerms (ZExpr.var i)) := by
  change vars i ≈z Zadd (Zmul (vars i) Zone) Zzero
  exact zring.symm
    (zring.trans (zring.add_zero (Zmul (vars i) Zone))
      (zMul_one (vars i)))

private theorem zExprTerms_sound :
    ∀ (vars : Nat -> Z) (e : ZExpr),
      zExprEval vars e ≈z zSumTerms vars (zExprTerms e)
  | vars, ZExpr.var i =>
      zExprTerms_sound_var vars i
  | vars, ZExpr.add a b => by
      exact zring.trans
        (zring.add_congr (zExprTerms_sound vars a) (zExprTerms_sound vars b))
        (zring.symm (zSum_append vars (zExprTerms a) (zExprTerms b)))
  | vars, ZExpr.mul a b => by
      exact zring.trans
        (zring.mul_congr (zExprTerms_sound vars a) (zExprTerms_sound vars b))
        (zring.symm (zTermsMul_sound vars (zExprTerms a) (zExprTerms b)))
  | vars, ZExpr.neg a => by
      exact zring.trans (zring.neg_congr (zExprTerms_sound vars a))
        (zring.symm (zSum_neg vars (zExprTerms a)))

private theorem zExprNorm_sound (vars : Nat -> Z) (e : ZExpr) :
    zExprEval vars e ≈z zSumTerms vars (zExprNorm e) := by
  exact zring.trans (zExprTerms_sound vars e)
    (zring.trans
      (zring.symm (zSum_canonical vars (zExprTerms e)))
      (zring.trans
        (zring.symm (zSum_sort vars (List.map zTermCanonical (zExprTerms e))))
        (zring.symm
          (zCancelTerms_sound vars
            (zTermSort (List.map zTermCanonical (zExprTerms e)))))))

private theorem zExpr_same_norm (vars : Nat -> Z) (a b : ZExpr)
    (h : zExprNorm a = zExprNorm b) :
    zExprEval vars a ≈z zExprEval vars b := by
  have left := zExprNorm_sound vars a
  have right := zExprNorm_sound vars b
  rw [h] at left
  exact zring.trans left (zring.symm right)

private structure QuatExpr where
  re : ZExpr
  imI : ZExpr
  imJ : ZExpr
  imK : ZExpr

private structure OctExpr where
  fst : QuatExpr
  snd : QuatExpr

private def qE (a b c d : Nat) : QuatExpr :=
  { re := ZExpr.var a, imI := ZExpr.var b, imJ := ZExpr.var c, imK := ZExpr.var d }

private def oExprX : OctExpr :=
  { fst := qE 0 1 2 3, snd := qE 4 5 6 7 }

private def oExprY : OctExpr :=
  { fst := qE 8 9 10 11, snd := qE 12 13 14 15 }

private def oExprZ : OctExpr :=
  { fst := qE 16 17 18 19, snd := qE 20 21 22 23 }

private def qExprAdd (x y : QuatExpr) : QuatExpr :=
  { re := ZExpr.add x.re y.re
    imI := ZExpr.add x.imI y.imI
    imJ := ZExpr.add x.imJ y.imJ
    imK := ZExpr.add x.imK y.imK }

private def qExprNeg (x : QuatExpr) : QuatExpr :=
  { re := ZExpr.neg x.re
    imI := ZExpr.neg x.imI
    imJ := ZExpr.neg x.imJ
    imK := ZExpr.neg x.imK }

private def qExprSub (x y : QuatExpr) : QuatExpr :=
  qExprAdd x (qExprNeg y)

private def qExprConj (x : QuatExpr) : QuatExpr :=
  { re := x.re
    imI := ZExpr.neg x.imI
    imJ := ZExpr.neg x.imJ
    imK := ZExpr.neg x.imK }

private def qExprMul (x y : QuatExpr) : QuatExpr :=
  { re := eSub (eSub (eSub (ZExpr.mul x.re y.re) (ZExpr.mul x.imI y.imI))
      (ZExpr.mul x.imJ y.imJ)) (ZExpr.mul x.imK y.imK)
    imI := ZExpr.add (ZExpr.add (ZExpr.mul x.re y.imI) (ZExpr.mul x.imI y.re))
      (eSub (ZExpr.mul x.imJ y.imK) (ZExpr.mul x.imK y.imJ))
    imJ := ZExpr.add (eSub (ZExpr.mul x.re y.imJ) (ZExpr.mul x.imI y.imK))
      (ZExpr.add (ZExpr.mul x.imJ y.re) (ZExpr.mul x.imK y.imI))
    imK := ZExpr.add (ZExpr.add (ZExpr.mul x.re y.imK) (ZExpr.mul x.imI y.imJ))
      (eSub (ZExpr.mul x.imK y.re) (ZExpr.mul x.imJ y.imI)) }

private def qExprNorm (x : QuatExpr) : ZExpr :=
  ZExpr.add (ZExpr.add (ZExpr.mul x.re x.re) (ZExpr.mul x.imI x.imI))
    (ZExpr.add (ZExpr.mul x.imJ x.imJ) (ZExpr.mul x.imK x.imK))

private def oExprAdd (x y : OctExpr) : OctExpr :=
  { fst := qExprAdd x.fst y.fst
    snd := qExprAdd x.snd y.snd }

private def oExprMul (x y : OctExpr) : OctExpr :=
  { fst := qExprSub (qExprMul x.fst y.fst) (qExprMul (qExprConj y.snd) x.snd)
    snd := qExprAdd (qExprMul y.snd x.fst) (qExprMul x.snd (qExprConj y.fst)) }

private def oExprNorm (x : OctExpr) : ZExpr :=
  ZExpr.add (qExprNorm x.fst) (qExprNorm x.snd)

private def octExprVars (x y z : Oct) : Nat -> Z
  | 0 => x.fst.re
  | 1 => x.fst.imI
  | 2 => x.fst.imJ
  | 3 => x.fst.imK
  | 4 => x.snd.re
  | 5 => x.snd.imI
  | 6 => x.snd.imJ
  | 7 => x.snd.imK
  | 8 => y.fst.re
  | 9 => y.fst.imI
  | 10 => y.fst.imJ
  | 11 => y.fst.imK
  | 12 => y.snd.re
  | 13 => y.snd.imI
  | 14 => y.snd.imJ
  | 15 => y.snd.imK
  | 16 => z.fst.re
  | 17 => z.fst.imI
  | 18 => z.fst.imJ
  | 19 => z.fst.imK
  | 20 => z.snd.re
  | 21 => z.snd.imI
  | 22 => z.snd.imJ
  | 23 => z.snd.imK
  | _ => Zzero

private theorem octNorm_mul_raw (x y : Oct) :
    octNorm (octMul x y) ≈z Zmul (octNorm x) (octNorm y) := by
  let vars := octExprVars x y octZero
  change zExprEval vars (oExprNorm (oExprMul oExprX oExprY)) ≈z
    zExprEval vars (ZExpr.mul (oExprNorm oExprX) (oExprNorm oExprY))
  exact zExpr_same_norm vars _ _ rfl

theorem octNorm_mul (x y : Oct) :
    octNorm (octMul x y) ≈z Zmul (octNorm x) (octNorm y) :=
  octNorm_mul_raw x y

end BEDC.Derived.OctonionUp
