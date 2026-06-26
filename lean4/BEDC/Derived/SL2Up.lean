import BEDC.Derived.MatrixUp
import BEDC.Algebra.Rel.IntegerUp

namespace BEDC.Derived.SL2Up

abbrev Mat2 := BEDC.Derived.MatrixUp.Mat2
abbrev MatEq := BEDC.Derived.MatrixUp.MatEq
abbrev matOne := BEDC.Derived.MatrixUp.matOne
abbrev matMul := BEDC.Derived.MatrixUp.matMul
abbrev det := BEDC.Derived.MatrixUp.det

private abbrev I := BEDC.Derived.PrimeUp.IntegerUp
private abbrev ieq := BEDC.Derived.RationalUp.IntEq
private abbrev iadd := BEDC.Derived.RationalUp.IntAdd
private abbrev imul := BEDC.Derived.RationalUp.IntMul
private abbrev ineg := BEDC.Derived.RationalUp.IntNeg
private abbrev izero := BEDC.Derived.RationalUp.intZero
private abbrev ione := BEDC.Derived.RationalUp.intOne

private theorem ieq_refl (x : I) : ieq x x :=
  BEDC.Derived.RationalUp.IntEq_refl x

private theorem ieq_symm {x y : I} : ieq x y -> ieq y x :=
  BEDC.Derived.RationalUp.IntEq_symm

private theorem ieq_trans {x y z : I} : ieq x y -> ieq y z -> ieq x z :=
  BEDC.Derived.RationalUp.IntEq_trans

private theorem iadd_respects {a a' b b' : I} :
    ieq a a' -> ieq b b' -> ieq (iadd a b) (iadd a' b') :=
  BEDC.Derived.IntUp.IntAdd_respects

private theorem imul_respects {a a' b b' : I} :
    ieq a a' -> ieq b b' -> ieq (imul a b) (imul a' b') :=
  BEDC.Derived.IntUp.IntMul_respects

private theorem ineg_respects {a b : I} :
    ieq a b -> ieq (ineg a) (ineg b) :=
  BEDC.Derived.IntUp.IntNeg_respects

private theorem iadd_comm (a b : I) : ieq (iadd a b) (iadd b a) :=
  BEDC.Derived.IntUp.IntAdd_comm a b

private theorem iadd_neg (a : I) : ieq (iadd a (ineg a)) izero :=
  BEDC.Derived.IntUp.IntAdd_neg a

private theorem iadd_neg_left (a : I) : ieq (iadd (ineg a) a) izero :=
  BEDC.Derived.IntUp.IntegerUp_comm_ring_laws.neg_add a

private theorem imul_comm (a b : I) : ieq (imul a b) (imul b a) :=
  BEDC.Derived.IntUp.IntMul_comm a b

private theorem imul_one_left (a : I) : ieq (imul ione a) a :=
  BEDC.Derived.IntUp.IntegerUp_comm_ring_laws.one_mul a

private theorem imul_neg_left (a b : I) :
    ieq (imul (ineg a) b) (ineg (imul a b)) :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing.neg_mul a b

private theorem imul_neg_right (a b : I) :
    ieq (imul a (ineg b)) (ineg (imul a b)) :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing.mul_neg a b

private theorem imul_neg_neg (a b : I) :
    ieq (imul (ineg a) (ineg b)) (imul a b) :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing.neg_neg_mul_neg a b

def SL2Carrier (A : Mat2) : Prop :=
  ieq (det A) ione

structure SL2 where
  mat : Mat2
  det_one : SL2Carrier mat

def SL2Eq (X Y : SL2) : Prop :=
  MatEq X.mat Y.mat

theorem SL2Eq_refl (X : SL2) : SL2Eq X X :=
  BEDC.Derived.MatrixUp.MatEq_refl X.mat

theorem SL2Eq_symm {X Y : SL2} : SL2Eq X Y -> SL2Eq Y X :=
  BEDC.Derived.MatrixUp.MatEq_symm

theorem SL2Eq_trans {X Y Z : SL2} :
    SL2Eq X Y -> SL2Eq Y Z -> SL2Eq X Z :=
  BEDC.Derived.MatrixUp.MatEq_trans

theorem SL2Carrier_matOne : SL2Carrier matOne :=
  BEDC.Derived.MatrixUp.det_one

theorem SL2Carrier_matMul {A B : Mat2} :
    SL2Carrier A -> SL2Carrier B -> SL2Carrier (matMul A B) := by
  intro detA detB
  exact ieq_trans (BEDC.Derived.MatrixUp.det_mul A B)
    (ieq_trans (imul_respects detA detB) (imul_one_left ione))

def SL2One : SL2 :=
  { mat := matOne
    det_one := SL2Carrier_matOne }

def SL2Mul (X Y : SL2) : SL2 :=
  { mat := matMul X.mat Y.mat
    det_one := SL2Carrier_matMul X.det_one Y.det_one }

theorem SL2Mul_closed (X Y : SL2) :
    SL2Carrier (matMul X.mat Y.mat) :=
  (SL2Mul X Y).det_one

def sl2AdjugateMat (A : Mat2) : Mat2 :=
  { a00 := A.a11
    a01 := ineg A.a01
    a10 := ineg A.a10
    a11 := A.a00 }

theorem sl2Adjugate_respects {A B : Mat2} :
    MatEq A B -> MatEq (sl2AdjugateMat A) (sl2AdjugateMat B) := by
  intro same
  unfold MatEq at same ⊢
  unfold sl2AdjugateMat
  exact
    ⟨same.right.right.right,
      ineg_respects same.right.left,
      ineg_respects same.right.right.left,
      same.left⟩

theorem sl2Adjugate_det_eq (A : Mat2) :
    ieq (det (sl2AdjugateMat A)) (det A) := by
  unfold det sl2AdjugateMat
  exact iadd_respects
    (imul_comm A.a11 A.a00)
    (ineg_respects (imul_neg_neg A.a01 A.a10))

theorem sl2Adjugate_det_one {A : Mat2} :
    SL2Carrier A -> SL2Carrier (sl2AdjugateMat A) := by
  intro detA
  exact ieq_trans (sl2Adjugate_det_eq A) detA

private theorem adj_left_entry00 (A : Mat2) :
    SL2Carrier A ->
      ieq (iadd (imul A.a11 A.a00) (imul (ineg A.a01) A.a10)) ione := by
  intro detA
  exact ieq_trans
    (iadd_respects (imul_comm A.a11 A.a00) (imul_neg_left A.a01 A.a10))
    detA

private theorem adj_left_entry01 (A : Mat2) :
    ieq (iadd (imul A.a11 A.a01) (imul (ineg A.a01) A.a11)) izero := by
  exact ieq_trans
    (iadd_respects (imul_comm A.a11 A.a01) (imul_neg_left A.a01 A.a11))
    (iadd_neg (imul A.a01 A.a11))

private theorem adj_left_entry10 (A : Mat2) :
    ieq (iadd (imul (ineg A.a10) A.a00) (imul A.a00 A.a10)) izero := by
  exact ieq_trans
    (iadd_respects (imul_neg_left A.a10 A.a00) (imul_comm A.a00 A.a10))
    (iadd_neg_left (imul A.a10 A.a00))

private theorem adj_left_entry11 (A : Mat2) :
    SL2Carrier A ->
      ieq (iadd (imul (ineg A.a10) A.a01) (imul A.a00 A.a11)) ione := by
  intro detA
  have first :
      ieq (imul (ineg A.a10) A.a01) (ineg (imul A.a01 A.a10)) :=
    ieq_trans (imul_neg_left A.a10 A.a01)
      (ineg_respects (imul_comm A.a10 A.a01))
  have reordered :
      ieq (iadd (imul (ineg A.a10) A.a01) (imul A.a00 A.a11))
        (iadd (imul A.a00 A.a11) (ineg (imul A.a01 A.a10))) :=
    ieq_trans
      (iadd_respects first (ieq_refl (imul A.a00 A.a11)))
      (iadd_comm (ineg (imul A.a01 A.a10)) (imul A.a00 A.a11))
  exact ieq_trans reordered detA

theorem sl2Adjugate_mul_left (A : Mat2) :
    SL2Carrier A -> MatEq (matMul (sl2AdjugateMat A) A) matOne := by
  intro detA
  unfold MatEq matMul sl2AdjugateMat matOne
  exact
    ⟨adj_left_entry00 A detA,
      adj_left_entry01 A,
      adj_left_entry10 A,
      adj_left_entry11 A detA⟩

private theorem adj_right_entry00 (A : Mat2) :
    SL2Carrier A ->
      ieq (iadd (imul A.a00 A.a11) (imul A.a01 (ineg A.a10))) ione := by
  intro detA
  exact ieq_trans
    (iadd_respects (ieq_refl (imul A.a00 A.a11)) (imul_neg_right A.a01 A.a10))
    detA

private theorem adj_right_entry01 (A : Mat2) :
    ieq (iadd (imul A.a00 (ineg A.a01)) (imul A.a01 A.a00)) izero := by
  exact ieq_trans
    (iadd_respects (imul_neg_right A.a00 A.a01) (imul_comm A.a01 A.a00))
    (iadd_neg_left (imul A.a00 A.a01))

private theorem adj_right_entry10 (A : Mat2) :
    ieq (iadd (imul A.a10 A.a11) (imul A.a11 (ineg A.a10))) izero := by
  have negTerm :
      ieq (imul A.a11 (ineg A.a10)) (ineg (imul A.a10 A.a11)) :=
    ieq_trans (imul_neg_right A.a11 A.a10)
      (ineg_respects (imul_comm A.a11 A.a10))
  exact ieq_trans
    (iadd_respects (ieq_refl (imul A.a10 A.a11)) negTerm)
    (iadd_neg (imul A.a10 A.a11))

private theorem adj_right_entry11 (A : Mat2) :
    SL2Carrier A ->
      ieq (iadd (imul A.a10 (ineg A.a01)) (imul A.a11 A.a00)) ione := by
  intro detA
  have first :
      ieq (imul A.a10 (ineg A.a01)) (ineg (imul A.a01 A.a10)) :=
    ieq_trans (imul_neg_right A.a10 A.a01)
      (ineg_respects (imul_comm A.a10 A.a01))
  have second :
      ieq (imul A.a11 A.a00) (imul A.a00 A.a11) :=
    imul_comm A.a11 A.a00
  have reordered :
      ieq (iadd (imul A.a10 (ineg A.a01)) (imul A.a11 A.a00))
        (iadd (imul A.a00 A.a11) (ineg (imul A.a01 A.a10))) :=
    ieq_trans
      (iadd_respects first second)
      (iadd_comm (ineg (imul A.a01 A.a10)) (imul A.a00 A.a11))
  exact ieq_trans reordered detA

theorem sl2Adjugate_mul_right (A : Mat2) :
    SL2Carrier A -> MatEq (matMul A (sl2AdjugateMat A)) matOne := by
  intro detA
  unfold MatEq matMul sl2AdjugateMat matOne
  exact
    ⟨adj_right_entry00 A detA,
      adj_right_entry01 A,
      adj_right_entry10 A,
      adj_right_entry11 A detA⟩

def SL2Inv (X : SL2) : SL2 :=
  { mat := sl2AdjugateMat X.mat
    det_one := sl2Adjugate_det_one X.det_one }

theorem SL2Inv_respects {X Y : SL2} :
    SL2Eq X Y -> SL2Eq (SL2Inv X) (SL2Inv Y) :=
  sl2Adjugate_respects

theorem SL2One_mul (X : SL2) :
    SL2Eq (SL2Mul SL2One X) X :=
  BEDC.Derived.MatrixUp.matOne_mul X.mat

theorem SL2Mul_one (X : SL2) :
    SL2Eq (SL2Mul X SL2One) X :=
  BEDC.Derived.MatrixUp.matMul_one X.mat

theorem SL2Mul_assoc (X Y Z : SL2) :
    SL2Eq (SL2Mul (SL2Mul X Y) Z) (SL2Mul X (SL2Mul Y Z)) :=
  BEDC.Derived.MatrixUp.matMul_assoc X.mat Y.mat Z.mat

theorem SL2Mul_respects {X X' Y Y' : SL2} :
    SL2Eq X X' -> SL2Eq Y Y' ->
      SL2Eq (SL2Mul X Y) (SL2Mul X' Y') :=
  BEDC.Derived.MatrixUp.matMul_respects

theorem SL2Inv_mul (X : SL2) :
    SL2Eq (SL2Mul (SL2Inv X) X) SL2One :=
  sl2Adjugate_mul_left X.mat X.det_one

theorem SL2Mul_inv (X : SL2) :
    SL2Eq (SL2Mul X (SL2Inv X)) SL2One :=
  sl2Adjugate_mul_right X.mat X.det_one

structure SL2GroupLaws where
  eq_refl : forall X : SL2, SL2Eq X X
  eq_symm : forall {X Y : SL2}, SL2Eq X Y -> SL2Eq Y X
  eq_trans : forall {X Y Z : SL2}, SL2Eq X Y -> SL2Eq Y Z -> SL2Eq X Z
  mul_respects :
    forall {X X' Y Y' : SL2}, SL2Eq X X' -> SL2Eq Y Y' ->
      SL2Eq (SL2Mul X Y) (SL2Mul X' Y')
  inv_respects : forall {X Y : SL2}, SL2Eq X Y -> SL2Eq (SL2Inv X) (SL2Inv Y)
  one_mul : forall X : SL2, SL2Eq (SL2Mul SL2One X) X
  mul_one : forall X : SL2, SL2Eq (SL2Mul X SL2One) X
  mul_assoc :
    forall X Y Z : SL2,
      SL2Eq (SL2Mul (SL2Mul X Y) Z) (SL2Mul X (SL2Mul Y Z))
  inv_mul : forall X : SL2, SL2Eq (SL2Mul (SL2Inv X) X) SL2One
  mul_inv : forall X : SL2, SL2Eq (SL2Mul X (SL2Inv X)) SL2One

def SL2_group_laws : SL2GroupLaws where
  eq_refl := SL2Eq_refl
  eq_symm := by
    intro X Y
    exact SL2Eq_symm
  eq_trans := by
    intro X Y Z
    exact SL2Eq_trans
  mul_respects := by
    intro X X' Y Y'
    exact SL2Mul_respects
  inv_respects := by
    intro X Y
    exact SL2Inv_respects
  one_mul := SL2One_mul
  mul_one := SL2Mul_one
  mul_assoc := SL2Mul_assoc
  inv_mul := SL2Inv_mul
  mul_inv := SL2Mul_inv

end BEDC.Derived.SL2Up
