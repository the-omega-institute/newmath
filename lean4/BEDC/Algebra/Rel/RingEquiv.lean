import BEDC.Algebra.Rel.Basic

namespace BEDC.Algebra.Rel

structure RelRingEquiv
    (A : Type u) (rA : A -> A -> Prop)
    (B : Type v) (rB : B -> B -> Prop) where
  source : RelRing A rA
  target : RelRing B rB
  toFun : A -> B
  invFun : B -> A
  map_rel : ∀ {x y : A}, rA x y -> rB (toFun x) (toFun y)
  inv_rel : ∀ {x y : B}, rB x y -> rA (invFun x) (invFun y)
  left_inv_rel : ∀ x : A, rA (invFun (toFun x)) x
  right_inv_rel : ∀ y : B, rB (toFun (invFun y)) y
  map_zero : rB (toFun source.zero) target.zero
  map_one : rB (toFun source.one) target.one
  map_add :
    ∀ x y : A, rB (toFun (source.add x y)) (target.add (toFun x) (toFun y))
  map_mul :
    ∀ x y : A, rB (toFun (source.mul x y)) (target.mul (toFun x) (toFun y))

namespace RelRingEquiv

variable {A : Type u} {B : Type v}
variable {rA : A -> A -> Prop} {rB : B -> B -> Prop}
variable (e : RelRingEquiv A rA B rB)

theorem map_sub
    (x y : A) :
    rB (e.toFun (e.source.sub x y))
      (e.target.add (e.toFun x) (e.target.neg (e.toFun y))) := by
  have negImage :
      rB (e.toFun (e.source.neg y)) (e.target.neg (e.toFun y)) :=
    e.target.eq_neg_of_add_eq_zero
      (a := e.toFun y)
      (b := e.toFun (e.source.neg y))
      (e.target.trans (e.target.symm (e.map_add y (e.source.neg y)))
        (e.target.trans (e.map_rel (e.source.add_neg y))
          e.map_zero))
  exact e.target.trans (e.map_rel (e.source.sub_eq_add_neg x y))
    (e.target.trans (e.map_add x (e.source.neg y))
      (e.target.add_left_congr (e.toFun x) negImage))

end RelRingEquiv

end BEDC.Algebra.Rel
