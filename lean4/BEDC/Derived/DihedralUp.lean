import BEDC.Derived.CyclicGroupUp

namespace BEDC.Derived.DihedralUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp
open BEDC.Derived.ZModUp
open BEDC.Derived.CyclicGroupUp

inductive DihedralSide where
  | rot
  | ref
  deriving DecidableEq, Repr

structure DihedralElement (n : BHist) where
  side : DihedralSide
  index : ZMod n

def dihedralEq {n : BHist} (x y : DihedralElement n) : Prop :=
  x.side = y.side ∧ zmodEq x.index y.index

def dihedralRot {n : BHist} (i : ZMod n) : DihedralElement n :=
  { side := DihedralSide.rot, index := i }

def dihedralRef {n : BHist} (i : ZMod n) : DihedralElement n :=
  { side := DihedralSide.ref, index := i }

def dihedralOne (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) : DihedralElement n :=
  dihedralRot (zmodZero n nUnary nNonempty)

def dihedralMul (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (x y : DihedralElement n) : DihedralElement n :=
  match x.side, y.side with
  | DihedralSide.rot, DihedralSide.rot =>
      dihedralRot (zmodAdd n nUnary nNonempty x.index y.index)
  | DihedralSide.rot, DihedralSide.ref =>
      dihedralRef (zmodAdd n nUnary nNonempty y.index (zmodNeg n nUnary nNonempty x.index))
  | DihedralSide.ref, DihedralSide.rot =>
      dihedralRef (zmodAdd n nUnary nNonempty x.index y.index)
  | DihedralSide.ref, DihedralSide.ref =>
      dihedralRot (zmodAdd n nUnary nNonempty y.index (zmodNeg n nUnary nNonempty x.index))

def dihedralInv (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (x : DihedralElement n) : DihedralElement n :=
  match x.side with
  | DihedralSide.rot => dihedralRot (zmodNeg n nUnary nNonempty x.index)
  | DihedralSide.ref => x

theorem dihedralEq_refl {n : BHist} (x : DihedralElement n) :
    dihedralEq x x := by
  exact ⟨rfl, zmodEq_refl x.index⟩

theorem dihedralEq_symm {n : BHist} {x y : DihedralElement n} :
    dihedralEq x y -> dihedralEq y x := by
  intro same
  exact ⟨same.left.symm, zmodEq_symm same.right⟩

theorem dihedralEq_trans {n : BHist} {x y z : DihedralElement n} :
    dihedralEq x y -> dihedralEq y z -> dihedralEq x z := by
  intro sameXY sameYZ
  exact ⟨sameXY.left.trans sameYZ.left, zmodEq_trans sameXY.right sameYZ.right⟩

theorem dihedralMul_respects {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    {x x' y y' : DihedralElement n} :
    dihedralEq x x' -> dihedralEq y y' ->
      dihedralEq (dihedralMul n nUnary nNonempty x y)
        (dihedralMul n nUnary nNonempty x' y') := by
  intro sameX sameY
  cases x with
  | mk xSide xIndex =>
      cases x' with
      | mk xSide' xIndex' =>
          cases y with
          | mk ySide yIndex =>
              cases y' with
              | mk ySide' yIndex' =>
                  dsimp [dihedralEq] at sameX sameY
                  cases sameX.left
                  cases sameY.left
                  cases xSide <;> cases ySide
                  · exact ⟨rfl, zmodAdd_congr nUnary nNonempty sameX.right sameY.right⟩
                  · exact ⟨rfl,
                      zmodAdd_congr nUnary nNonempty sameY.right
                        (zmodNeg_congr nUnary nNonempty sameX.right)⟩
                  · exact ⟨rfl, zmodAdd_congr nUnary nNonempty sameX.right sameY.right⟩
                  · exact ⟨rfl,
                      zmodAdd_congr nUnary nNonempty sameY.right
                        (zmodNeg_congr nUnary nNonempty sameX.right)⟩

theorem dihedralRot_mul_rot {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (i j : ZMod n) :
    dihedralEq
      (dihedralMul n nUnary nNonempty (dihedralRot i) (dihedralRot j))
      (dihedralRot (zmodAdd n nUnary nNonempty i j)) := by
  exact dihedralEq_refl _

theorem dihedralRef_mul_rot {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (i j : ZMod n) :
    dihedralEq
      (dihedralMul n nUnary nNonempty (dihedralRef i) (dihedralRot j))
      (dihedralRef (zmodAdd n nUnary nNonempty i j)) := by
  exact dihedralEq_refl _

theorem dihedralRot_mul_ref {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (i j : ZMod n) :
    dihedralEq
      (dihedralMul n nUnary nNonempty (dihedralRot i) (dihedralRef j))
      (dihedralRef
        (zmodAdd n nUnary nNonempty j (zmodNeg n nUnary nNonempty i))) := by
  exact dihedralEq_refl _

theorem dihedralRef_mul_ref {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (i j : ZMod n) :
    dihedralEq
      (dihedralMul n nUnary nNonempty (dihedralRef i) (dihedralRef j))
      (dihedralRot
        (zmodAdd n nUnary nNonempty j (zmodNeg n nUnary nNonempty i))) := by
  exact dihedralEq_refl _

private theorem zmodAdd_assoc_swap_last {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (a b c : ZMod n) :
    zmodEq
      (zmodAdd n nUnary nNonempty (zmodAdd n nUnary nNonempty a b) c)
      (zmodAdd n nUnary nNonempty (zmodAdd n nUnary nNonempty a c) b) := by
  exact zmodEq_trans
    (zmodAdd_assoc nUnary nNonempty a b c)
    (zmodEq_trans
      (zmodAdd_congr nUnary nNonempty (zmodEq_refl a)
        (zmodAdd_comm nUnary nNonempty b c))
      (zmodEq_symm (zmodAdd_assoc nUnary nNonempty a c b)))

private theorem zmodAdd_neg_nested_cancel {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (a b : ZMod n) :
    zmodEq
      (zmodAdd n nUnary nNonempty
        (zmodAdd n nUnary nNonempty a (zmodNeg n nUnary nNonempty b)) b)
      a := by
  exact zmodEq_trans
    (zmodAdd_assoc nUnary nNonempty a (zmodNeg n nUnary nNonempty b) b)
    (zmodEq_trans
      (zmodAdd_congr nUnary nNonempty (zmodEq_refl a)
        (zmodAdd_neg_left nUnary nNonempty b))
      (zmodZero_add_right nUnary nNonempty a))

private theorem zmodAdd_neg_nested_cancel_left {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (a b : ZMod n) :
    zmodEq
      (zmodAdd n nUnary nNonempty
        (zmodAdd n nUnary nNonempty a b) (zmodNeg n nUnary nNonempty b))
      a := by
  exact zmodEq_trans
    (zmodAdd_assoc nUnary nNonempty a b (zmodNeg n nUnary nNonempty b))
    (zmodEq_trans
      (zmodAdd_congr nUnary nNonempty (zmodEq_refl a)
        (zmodAdd_neg_right nUnary nNonempty b))
      (zmodZero_add_right nUnary nNonempty a))

private theorem zmodEq_eq_neg_of_add_eq_zero {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (a b : ZMod n) :
    zmodEq (zmodAdd n nUnary nNonempty a b) (zmodZero n nUnary nNonempty) ->
      zmodEq b (zmodNeg n nUnary nNonempty a) := by
  intro addZero
  exact zmodEq_trans
    (zmodEq_symm (zmodZero_add_left nUnary nNonempty b))
    (zmodEq_trans
      (zmodAdd_congr nUnary nNonempty
        (zmodEq_symm (zmodAdd_neg_left nUnary nNonempty a)) (zmodEq_refl b))
      (zmodEq_trans
        (zmodAdd_assoc nUnary nNonempty (zmodNeg n nUnary nNonempty a) a b)
        (zmodEq_trans
          (zmodAdd_congr nUnary nNonempty (zmodEq_refl _ ) addZero)
          (zmodZero_add_right nUnary nNonempty (zmodNeg n nUnary nNonempty a)))))

private theorem zmodEq_neg_eq_of_add_eq_zero {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (a b : ZMod n) :
    zmodEq (zmodAdd n nUnary nNonempty a b) (zmodZero n nUnary nNonempty) ->
      zmodEq (zmodNeg n nUnary nNonempty a) b := by
  intro addZero
  exact zmodEq_symm (zmodEq_eq_neg_of_add_eq_zero nUnary nNonempty a b addZero)

private theorem zmodNeg_zero {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) :
    zmodEq (zmodNeg n nUnary nNonempty (zmodZero n nUnary nNonempty))
      (zmodZero n nUnary nNonempty) := by
  exact zmodEq_trans
    (zmodEq_symm (zmodZero_add_right nUnary nNonempty
      (zmodNeg n nUnary nNonempty (zmodZero n nUnary nNonempty))))
    (zmodAdd_neg_left nUnary nNonempty (zmodZero n nUnary nNonempty))

private theorem zmodNeg_add_hom {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (a b : ZMod n) :
    zmodEq
      (zmodNeg n nUnary nNonempty (zmodAdd n nUnary nNonempty a b))
      (zmodAdd n nUnary nNonempty
        (zmodNeg n nUnary nNonempty a) (zmodNeg n nUnary nNonempty b)) := by
  have sumRightZero :
      zmodEq
        (zmodAdd n nUnary nNonempty
          (zmodAdd n nUnary nNonempty a b)
          (zmodAdd n nUnary nNonempty
            (zmodNeg n nUnary nNonempty a) (zmodNeg n nUnary nNonempty b)))
        (zmodZero n nUnary nNonempty) := by
    exact zmodEq_trans
      (zmodEq_symm (zmodAdd_assoc nUnary nNonempty
        (zmodAdd n nUnary nNonempty a b)
        (zmodNeg n nUnary nNonempty a)
        (zmodNeg n nUnary nNonempty b)))
      (zmodEq_trans
        (zmodAdd_congr nUnary nNonempty
          (zmodAdd_assoc_swap_last nUnary nNonempty a b
            (zmodNeg n nUnary nNonempty a))
          (zmodEq_refl _))
        (zmodEq_trans
          (zmodAdd_congr nUnary nNonempty
            (zmodEq_trans
              (zmodAdd_congr nUnary nNonempty
                (zmodAdd_neg_right nUnary nNonempty a) (zmodEq_refl b))
              (zmodZero_add_left nUnary nNonempty b))
            (zmodEq_refl _))
          (zmodAdd_neg_right nUnary nNonempty b)))
  exact zmodEq_neg_eq_of_add_eq_zero nUnary nNonempty
    (zmodAdd n nUnary nNonempty a b)
    (zmodAdd n nUnary nNonempty
      (zmodNeg n nUnary nNonempty a) (zmodNeg n nUnary nNonempty b))
    sumRightZero

private theorem zmodNeg_neg {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (a : ZMod n) :
    zmodEq
      (zmodNeg n nUnary nNonempty (zmodNeg n nUnary nNonempty a)) a := by
  exact zmodEq_neg_eq_of_add_eq_zero nUnary nNonempty
    (zmodNeg n nUnary nNonempty a) a
    (zmodAdd_neg_left nUnary nNonempty a)

private theorem zmodNeg_add_cancel_pair {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (a b : ZMod n) :
    zmodEq
      (zmodAdd n nUnary nNonempty
        (zmodNeg n nUnary nNonempty
          (zmodAdd n nUnary nNonempty a b)) a)
      (zmodNeg n nUnary nNonempty b) := by
  exact zmodEq_trans
    (zmodAdd_congr nUnary nNonempty
      (zmodNeg_add_hom nUnary nNonempty a b) (zmodEq_refl a))
    (zmodEq_trans
      (zmodAdd_assoc_swap_last nUnary nNonempty
        (zmodNeg n nUnary nNonempty a)
        (zmodNeg n nUnary nNonempty b) a)
      (zmodEq_trans
        (zmodAdd_congr nUnary nNonempty
          (zmodAdd_neg_left nUnary nNonempty a) (zmodEq_refl _))
        (zmodZero_add_left nUnary nNonempty
          (zmodNeg n nUnary nNonempty b))))

private theorem zmodAssoc_rrr {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (a b c : ZMod n) :
    zmodEq (zmodAdd n nUnary nNonempty (zmodAdd n nUnary nNonempty a b) c)
      (zmodAdd n nUnary nNonempty a (zmodAdd n nUnary nNonempty b c)) :=
  zmodAdd_assoc nUnary nNonempty a b c

private theorem zmodAssoc_rrf {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (a b c : ZMod n) :
    zmodEq
      (zmodAdd n nUnary nNonempty c
        (zmodNeg n nUnary nNonempty (zmodAdd n nUnary nNonempty a b)))
      (zmodAdd n nUnary nNonempty
        (zmodAdd n nUnary nNonempty c (zmodNeg n nUnary nNonempty b))
        (zmodNeg n nUnary nNonempty a)) := by
  exact zmodEq_trans
    (zmodAdd_congr nUnary nNonempty (zmodEq_refl c)
      (zmodNeg_add_hom nUnary nNonempty a b))
    (zmodEq_trans
      (zmodEq_symm (zmodAdd_assoc nUnary nNonempty c
        (zmodNeg n nUnary nNonempty a) (zmodNeg n nUnary nNonempty b))
      )
      (zmodAdd_assoc_swap_last nUnary nNonempty c
        (zmodNeg n nUnary nNonempty a) (zmodNeg n nUnary nNonempty b)))

private theorem zmodAssoc_rfr {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (a b c : ZMod n) :
    zmodEq
      (zmodAdd n nUnary nNonempty
        (zmodAdd n nUnary nNonempty b (zmodNeg n nUnary nNonempty a)) c)
      (zmodAdd n nUnary nNonempty
        (zmodAdd n nUnary nNonempty b c)
        (zmodNeg n nUnary nNonempty a)) :=
  zmodAdd_assoc_swap_last nUnary nNonempty b (zmodNeg n nUnary nNonempty a) c

private theorem zmodAssoc_rff {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (a b c : ZMod n) :
    zmodEq
      (zmodAdd n nUnary nNonempty c
        (zmodNeg n nUnary nNonempty
          (zmodAdd n nUnary nNonempty b (zmodNeg n nUnary nNonempty a))))
      (zmodAdd n nUnary nNonempty
        a (zmodAdd n nUnary nNonempty c (zmodNeg n nUnary nNonempty b))) := by
  exact zmodEq_trans
    (zmodAdd_congr nUnary nNonempty (zmodEq_refl c)
      (zmodNeg_add_hom nUnary nNonempty b (zmodNeg n nUnary nNonempty a)))
    (zmodEq_trans
      (zmodEq_symm (zmodAdd_assoc nUnary nNonempty c
        (zmodNeg n nUnary nNonempty b)
        (zmodNeg n nUnary nNonempty (zmodNeg n nUnary nNonempty a))))
      (zmodEq_trans
        (zmodAdd_congr nUnary nNonempty (zmodEq_refl _)
          (zmodNeg_neg nUnary nNonempty a))
        (zmodAdd_comm nUnary nNonempty
          (zmodAdd n nUnary nNonempty c (zmodNeg n nUnary nNonempty b)) a)))

theorem dihedralMul_assoc {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (x y z : DihedralElement n) :
    dihedralEq
      (dihedralMul n nUnary nNonempty (dihedralMul n nUnary nNonempty x y) z)
      (dihedralMul n nUnary nNonempty x (dihedralMul n nUnary nNonempty y z)) := by
  cases x with
  | mk xSide xIndex =>
      cases y with
      | mk ySide yIndex =>
          cases z with
          | mk zSide zIndex =>
              cases xSide <;> cases ySide <;> cases zSide
              · exact ⟨rfl, zmodAssoc_rrr nUnary nNonempty xIndex yIndex zIndex⟩
              · exact ⟨rfl, zmodAssoc_rrf nUnary nNonempty xIndex yIndex zIndex⟩
              · exact ⟨rfl, zmodAssoc_rfr nUnary nNonempty xIndex yIndex zIndex⟩
              · exact ⟨rfl, zmodAssoc_rff nUnary nNonempty xIndex yIndex zIndex⟩
              · exact ⟨rfl, zmodAssoc_rrr nUnary nNonempty xIndex yIndex zIndex⟩
              · exact ⟨rfl, zmodAssoc_rrf nUnary nNonempty xIndex yIndex zIndex⟩
              · exact ⟨rfl, zmodAssoc_rfr nUnary nNonempty xIndex yIndex zIndex⟩
              · exact ⟨rfl, zmodAssoc_rff nUnary nNonempty xIndex yIndex zIndex⟩

theorem dihedralOne_mul {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (x : DihedralElement n) :
    dihedralEq (dihedralMul n nUnary nNonempty
      (dihedralOne n nUnary nNonempty) x) x := by
  cases x with
  | mk side index =>
      cases side
      · exact ⟨rfl, zmodZero_add_left nUnary nNonempty index⟩
      · exact ⟨rfl, zmodEq_trans
          (zmodAdd_congr nUnary nNonempty (zmodEq_refl index)
            (zmodNeg_zero nUnary nNonempty))
          (zmodZero_add_right nUnary nNonempty index)⟩

theorem dihedralMul_one {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (x : DihedralElement n) :
    dihedralEq (dihedralMul n nUnary nNonempty x
      (dihedralOne n nUnary nNonempty)) x := by
  cases x with
  | mk side index =>
      cases side
      · exact ⟨rfl, zmodZero_add_right nUnary nNonempty index⟩
      · exact ⟨rfl, zmodZero_add_right nUnary nNonempty index⟩

theorem dihedralInv_mul {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (x : DihedralElement n) :
    dihedralEq
      (dihedralMul n nUnary nNonempty
        (dihedralInv n nUnary nNonempty x) x)
      (dihedralOne n nUnary nNonempty) := by
  cases x with
  | mk side index =>
      cases side
      · exact ⟨rfl, zmodAdd_neg_left nUnary nNonempty index⟩
      · exact ⟨rfl, zmodAdd_neg_right nUnary nNonempty index⟩

theorem dihedralMul_inv {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (x : DihedralElement n) :
    dihedralEq
      (dihedralMul n nUnary nNonempty x
        (dihedralInv n nUnary nNonempty x))
      (dihedralOne n nUnary nNonempty) := by
  cases x with
  | mk side index =>
      cases side
      · exact ⟨rfl, zmodAdd_neg_right nUnary nNonempty index⟩
      · exact ⟨rfl, zmodAdd_neg_right nUnary nNonempty index⟩

structure DihedralGroupCore (n : BHist) where
  n_unary : UnaryHistory n
  n_nonempty : hsame n BHist.Empty -> False
  carrier : Type
  eqv : carrier -> carrier -> Prop
  eq_refl : ∀ x : carrier, eqv x x
  eq_symm : ∀ {x y : carrier}, eqv x y -> eqv y x
  eq_trans : ∀ {x y z : carrier}, eqv x y -> eqv y z -> eqv x z
  one : carrier
  mul : carrier -> carrier -> carrier
  inv : carrier -> carrier
  mul_respects : ∀ {x x' y y' : carrier}, eqv x x' -> eqv y y' ->
    eqv (mul x y) (mul x' y')
  mul_assoc : ∀ x y z : carrier, eqv (mul (mul x y) z) (mul x (mul y z))
  one_mul : ∀ x : carrier, eqv (mul one x) x
  mul_one : ∀ x : carrier, eqv (mul x one) x
  inv_mul : ∀ x : carrier, eqv (mul (inv x) x) one
  mul_inv : ∀ x : carrier, eqv (mul x (inv x)) one

def dihedralGroupCore (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) : DihedralGroupCore n :=
  { n_unary := nUnary
    n_nonempty := nNonempty
    carrier := DihedralElement n
    eqv := dihedralEq
    eq_refl := dihedralEq_refl
    eq_symm := dihedralEq_symm
    eq_trans := dihedralEq_trans
    one := dihedralOne n nUnary nNonempty
    mul := dihedralMul n nUnary nNonempty
    inv := dihedralInv n nUnary nNonempty
    mul_respects := dihedralMul_respects nUnary nNonempty
    mul_assoc := dihedralMul_assoc nUnary nNonempty
    one_mul := dihedralOne_mul nUnary nNonempty
    mul_one := dihedralMul_one nUnary nNonempty
    inv_mul := dihedralInv_mul nUnary nNonempty
    mul_inv := dihedralMul_inv nUnary nNonempty }

structure DihedralOrderWitness (n : BHist) where
  total : BHist
  total_is_two_n : NatAdd n n total
  rotation_fiber : Type
  reflection_fiber : Type
  rotation_fiber_eq : rotation_fiber = ZMod n
  reflection_fiber_eq : reflection_fiber = ZMod n
  rotation_embed : rotation_fiber -> DihedralElement n
  reflection_embed : reflection_fiber -> DihedralElement n
  element_cover : ∀ x : DihedralElement n,
    (∃ i : rotation_fiber, dihedralEq x (rotation_embed i)) ∨
      (∃ i : reflection_fiber, dihedralEq x (reflection_embed i))
  fiber_disjoint : ∀ (i : rotation_fiber) (j : reflection_fiber),
    dihedralEq (rotation_embed i) (reflection_embed j) -> False

def dihedralOrderTwoMulModulus {n : BHist}
    (nUnary : UnaryHistory n) : DihedralOrderWitness n :=
  {
    total := append n n
    total_is_two_n := NatAdd_append_self nUnary nUnary
    rotation_fiber := ZMod n
    reflection_fiber := ZMod n
    rotation_fiber_eq := rfl
    reflection_fiber_eq := rfl
    rotation_embed := dihedralRot
    reflection_embed := dihedralRef
    element_cover := by
      intro x
      cases x with
      | mk side index =>
          cases side
          · exact Or.inl ⟨index, dihedralEq_refl _⟩
          · exact Or.inr ⟨index, dihedralEq_refl _⟩
    fiber_disjoint := by
      intro i j same
      cases same.left
  }

theorem dihedral_order_two_mul_modulus_exists {n : BHist} :
    UnaryHistory n -> Nonempty (DihedralOrderWitness n) := by
  intro nUnary
  exact ⟨dihedralOrderTwoMulModulus nUnary⟩

structure RotationSubgroupCore (n : BHist) where
  n_unary : UnaryHistory n
  n_nonempty : hsame n BHist.Empty -> False
  carrier : Type
  eqv : carrier -> carrier -> Prop
  one : carrier
  mul : carrier -> carrier -> carrier
  inv : carrier -> carrier
  embeds : carrier -> DihedralElement n
  embeds_respects : ∀ {x y : carrier}, eqv x y -> dihedralEq (embeds x) (embeds y)
  mul_closed : ∀ x y : carrier,
    dihedralEq (embeds (mul x y))
      (dihedralMul n n_unary n_nonempty (embeds x) (embeds y))
  one_closed : dihedralEq (embeds one) (dihedralOne n n_unary n_nonempty)
  inv_closed : ∀ x : carrier,
    dihedralEq (embeds (inv x))
      (dihedralInv n n_unary n_nonempty (embeds x))
  cyclic_generator : ∃ g : ZMod n,
    ZModGenerates n_unary n_nonempty g

def rotationSubgroupCore (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) : RotationSubgroupCore n :=
  { n_unary := nUnary
    n_nonempty := nNonempty
    carrier := ZMod n
    eqv := zmodEq
    one := zmodZero n nUnary nNonempty
    mul := zmodAdd n nUnary nNonempty
    inv := zmodNeg n nUnary nNonempty
    embeds := dihedralRot
    embeds_respects := by
      intro x y same
      exact ⟨rfl, same⟩
    mul_closed := by
      intro x y
      exact dihedralEq_refl _
    one_closed := dihedralEq_refl _
    inv_closed := by
      intro x
      exact dihedralEq_refl _
    cyclic_generator := zmod_cyclic_exists nUnary nNonempty }

def zmodTwo (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) : ZMod n :=
  zmodFromNat n nUnary nNonempty (BHist.e1 (BHist.e1 BHist.Empty))
    (unary_e1_closed (unary_e1_closed unary_empty))

def zmodThree (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) : ZMod n :=
  zmodFromNat n nUnary nNonempty (BHist.e1 (BHist.e1 (BHist.e1 BHist.Empty)))
    (unary_e1_closed (unary_e1_closed (unary_e1_closed unary_empty)))

def DihedralNoncommWitness (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) : Prop :=
  dihedralEq
    (dihedralMul n nUnary nNonempty
      (dihedralRot (zmodOne n nUnary nNonempty))
      (dihedralRef (zmodZero n nUnary nNonempty)))
    (dihedralMul n nUnary nNonempty
      (dihedralRef (zmodZero n nUnary nNonempty))
      (dihedralRot (zmodOne n nUnary nNonempty))) -> False

theorem dihedral_noncomm_witness_of_one_not_neg_one {n : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (one_ne_neg_one :
      zmodEq (zmodNeg n nUnary nNonempty (zmodOne n nUnary nNonempty))
        (zmodOne n nUnary nNonempty) -> False) :
    DihedralNoncommWitness n nUnary nNonempty := by
  intro same
  exact one_ne_neg_one
    (zmodEq_trans
      (zmodEq_symm (zmodZero_add_left nUnary nNonempty
        (zmodNeg n nUnary nNonempty (zmodOne n nUnary nNonempty))))
      (zmodEq_trans same.right
        (zmodZero_add_left nUnary nNonempty (zmodOne n nUnary nNonempty))))

end BEDC.Derived.DihedralUp
