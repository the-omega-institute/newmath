import BEDC.Algebra.FiniteFold
import BEDC.Algebra.Rel.IntegerUp
import BEDC.Derived.MatrixUp
import BEDC.Derived.PolynomialUp

namespace BEDC.Derived.VandermondeDeterminantUp

open BEDC.Algebra.FiniteFold
open BEDC.Algebra.Rel

inductive SmallVar : Type where
  | x0
  | x1
  | x2
  deriving DecidableEq

inductive VExpr : Type where
  | zero
  | one
  | var : SmallVar -> VExpr
  | add : VExpr -> VExpr -> VExpr
  | mul : VExpr -> VExpr -> VExpr
  | neg : VExpr -> VExpr
  deriving DecidableEq

namespace VExpr

def sub (a b : VExpr) : VExpr :=
  VExpr.add a (VExpr.neg b)

def pow : VExpr -> Nat -> VExpr
  | _x, 0 => VExpr.one
  | x, Nat.succ 0 => x
  | x, Nat.succ (Nat.succ n) => VExpr.mul (pow x (Nat.succ n)) x

def mul3 (a b c : VExpr) : VExpr :=
  VExpr.mul (VExpr.mul a b) c

end VExpr

structure Mono3 : Type where
  x0 : Nat
  x1 : Nat
  x2 : Nat
  deriving DecidableEq

namespace Mono3

def one : Mono3 :=
  { x0 := 0, x1 := 0, x2 := 0 }

def var : SmallVar -> Mono3
  | SmallVar.x0 => { x0 := 1, x1 := 0, x2 := 0 }
  | SmallVar.x1 => { x0 := 0, x1 := 1, x2 := 0 }
  | SmallVar.x2 => { x0 := 0, x1 := 0, x2 := 1 }

def mul (a b : Mono3) : Mono3 :=
  { x0 := a.x0 + b.x0, x1 := a.x1 + b.x1, x2 := a.x2 + b.x2 }

def lt (a b : Mono3) : Bool :=
  if a.x0 < b.x0 then
    true
  else if b.x0 < a.x0 then
    false
  else if a.x1 < b.x1 then
    true
  else if b.x1 < a.x1 then
    false
  else
    a.x2 < b.x2

end Mono3

inductive Sign : Type where
  | pos
  | neg
  deriving DecidableEq

namespace Sign

def flip : Sign -> Sign
  | Sign.pos => Sign.neg
  | Sign.neg => Sign.pos

def mul : Sign -> Sign -> Sign
  | Sign.pos, s => s
  | Sign.neg, Sign.pos => Sign.neg
  | Sign.neg, Sign.neg => Sign.pos

end Sign

structure SignedMono3 : Type where
  sign : Sign
  mono : Mono3
  deriving DecidableEq

abbrev VPoly := List SignedMono3

def signedOne : SignedMono3 :=
  { sign := Sign.pos, mono := Mono3.one }

def signedVar (v : SmallVar) : SignedMono3 :=
  { sign := Sign.pos, mono := Mono3.var v }

def signedNeg (t : SignedMono3) : SignedMono3 :=
  { sign := Sign.flip t.sign, mono := t.mono }

def signedMul (a b : SignedMono3) : SignedMono3 :=
  { sign := Sign.mul a.sign b.sign, mono := Mono3.mul a.mono b.mono }

def rawMulTerm (t : SignedMono3) : VPoly -> VPoly
  | [] => []
  | u :: us => signedMul t u :: rawMulTerm t us

def rawMul : VPoly -> VPoly -> VPoly
  | [], _ => []
  | t :: ts, us => rawMulTerm t us ++ rawMul ts us

def rawNeg : VPoly -> VPoly
  | [] => []
  | t :: ts => signedNeg t :: rawNeg ts

def raw : VExpr -> VPoly
  | VExpr.zero => []
  | VExpr.one => [signedOne]
  | VExpr.var v => [signedVar v]
  | VExpr.add a b => raw a ++ raw b
  | VExpr.mul a b => rawMul (raw a) (raw b)
  | VExpr.neg a => rawNeg (raw a)

def insertSigned (t : SignedMono3) : VPoly -> VPoly
  | [] => [t]
  | u :: us =>
      if t.mono = u.mono then
        if t.sign = u.sign then
          t :: u :: us
        else
          us
      else if Mono3.lt t.mono u.mono then
        t :: u :: us
      else
        u :: insertSigned t us

def canonical : VPoly -> VPoly
  | [] => []
  | t :: ts => insertSigned t (canonical ts)

def normal (e : VExpr) : VPoly :=
  canonical (raw e)

def x0 : VExpr := VExpr.var SmallVar.x0
def x1 : VExpr := VExpr.var SmallVar.x1
def x2 : VExpr := VExpr.var SmallVar.x2

def square (x : VExpr) : VExpr :=
  VExpr.mul x x

def fourTimes (x : VExpr) : VExpr :=
  VExpr.add x (VExpr.add x (VExpr.add x x))

def vandermondeRow (x : VExpr) : Nat -> List VExpr
  | 0 => []
  | Nat.succ n => vandermondeRow x n ++ [VExpr.pow x n]

def vandermondeMatrix (xs : List VExpr) (cols : Nat) : List (List VExpr) :=
  xs.map (fun x => vandermondeRow x cols)

def vandermonde2Matrix : List (List VExpr) :=
  vandermondeMatrix [x0, x1] 2

def vandermonde3Matrix : List (List VExpr) :=
  vandermondeMatrix [x0, x1, x2] 3

def det2Expr (a b c d : VExpr) : VExpr :=
  VExpr.sub (VExpr.mul a d) (VExpr.mul b c)

def det3Expr (a b c d e f g h i : VExpr) : VExpr :=
  VExpr.add
    (VExpr.add
      (VExpr.add (VExpr.mul3 a e i) (VExpr.mul3 b f g))
      (VExpr.mul3 c d h))
    (VExpr.neg
      (VExpr.add
        (VExpr.add (VExpr.mul3 c e g) (VExpr.mul3 b d i))
        (VExpr.mul3 a f h)))

def vandermonde2DetExpr : VExpr :=
  det2Expr VExpr.one x0 VExpr.one x1

def vandermonde3DetExpr : VExpr :=
  det3Expr
    VExpr.one x0 (square x0)
    VExpr.one x1 (square x1)
    VExpr.one x2 (square x2)

def pairProduct2Expr : VExpr :=
  VExpr.sub x1 x0

def pairProduct3Expr : VExpr :=
  VExpr.mul3 (VExpr.sub x1 x0) (VExpr.sub x2 x0) (VExpr.sub x2 x1)

def elementarySymmetric2One : VExpr :=
  VExpr.add x0 x1

def elementarySymmetric2Two : VExpr :=
  VExpr.mul x0 x1

def discriminant2Expr : VExpr :=
  square pairProduct2Expr

def discriminant3Expr : VExpr :=
  square pairProduct3Expr

def swap01 : VExpr -> VExpr
  | VExpr.zero => VExpr.zero
  | VExpr.one => VExpr.one
  | VExpr.var SmallVar.x0 => x1
  | VExpr.var SmallVar.x1 => x0
  | VExpr.var SmallVar.x2 => x2
  | VExpr.add a b => VExpr.add (swap01 a) (swap01 b)
  | VExpr.mul a b => VExpr.mul (swap01 a) (swap01 b)
  | VExpr.neg a => VExpr.neg (swap01 a)

def swap12 : VExpr -> VExpr
  | VExpr.zero => VExpr.zero
  | VExpr.one => VExpr.one
  | VExpr.var SmallVar.x0 => x0
  | VExpr.var SmallVar.x1 => x2
  | VExpr.var SmallVar.x2 => x1
  | VExpr.add a b => VExpr.add (swap12 a) (swap12 b)
  | VExpr.mul a b => VExpr.mul (swap12 a) (swap12 b)
  | VExpr.neg a => VExpr.neg (swap12 a)

def FormalPolynomialIdentity (lhs rhs : VExpr) : Prop :=
  normal lhs = normal rhs

theorem vandermonde2_matrix_shape :
    vandermonde2Matrix = [[VExpr.one, x0], [VExpr.one, x1]] := by
  rfl

theorem vandermonde3_matrix_shape :
    vandermonde3Matrix =
      [[VExpr.one, x0, square x0],
        [VExpr.one, x1, square x1],
        [VExpr.one, x2, square x2]] := by
  rfl

theorem vandermonde2_det_pair_product :
    FormalPolynomialIdentity vandermonde2DetExpr pairProduct2Expr := by
  rfl

theorem vandermonde3_det_pair_product :
    FormalPolynomialIdentity vandermonde3DetExpr pairProduct3Expr := by
  rfl

theorem vandermonde2_symmetric_square_discriminant :
    FormalPolynomialIdentity discriminant2Expr
      (VExpr.sub (square elementarySymmetric2One) (fourTimes elementarySymmetric2Two)) := by
  rfl

theorem vandermonde2_discriminant_swap01 :
    FormalPolynomialIdentity (swap01 discriminant2Expr) discriminant2Expr := by
  rfl

theorem vandermonde3_discriminant_swap01 :
    FormalPolynomialIdentity (swap01 discriminant3Expr) discriminant3Expr := by
  rfl

theorem vandermonde3_discriminant_swap12 :
    FormalPolynomialIdentity (swap12 discriminant3Expr) discriminant3Expr := by
  rfl

def pairFactors2Value {A : Type u} {r : A -> A -> Prop}
    (R : RelCommRing A r) (a b : A) : List A :=
  [R.sub b a]

def pairProduct2Value {A : Type u} {r : A -> A -> Prop}
    (R : RelCommRing A r) (a b : A) : A :=
  listProd R (pairFactors2Value R a b)

def vandermonde2DetValue {A : Type u} {r : A -> A -> Prop}
    (R : RelCommRing A r) (a b : A) : A :=
  R.sub (R.mul R.one b) (R.mul a R.one)

theorem pairProduct2Value_singleton {A : Type u} {r : A -> A -> Prop}
    (R : RelCommRing A r) (a b : A) :
    r (pairProduct2Value R a b) (R.sub b a) := by
  unfold pairProduct2Value pairFactors2Value
  exact R.mul_one (R.sub b a)

theorem vandermonde2_det_value_pair_product {A : Type u} {r : A -> A -> Prop}
    (R : RelCommRing A r) (a b : A) :
    r (vandermonde2DetValue R a b) (pairProduct2Value R a b) := by
  unfold vandermonde2DetValue
  exact R.trans
    (R.add_congr (R.one_mul b) (R.neg_congr (R.mul_one a)))
    (R.symm (pairProduct2Value_singleton R a b))

abbrev IntegerUp := BEDC.Algebra.Rel.IntegerUp
abbrev IntEq := BEDC.Algebra.Rel.IntEq

theorem IntegerUp_vandermonde2_det_pair_product (a b : IntegerUp) :
    IntEq
      (vandermonde2DetValue BEDC.Algebra.Rel.IntegerUp_RelCommRing a b)
      (pairProduct2Value BEDC.Algebra.Rel.IntegerUp_RelCommRing a b) :=
  vandermonde2_det_value_pair_product BEDC.Algebra.Rel.IntegerUp_RelCommRing a b

end BEDC.Derived.VandermondeDeterminantUp
