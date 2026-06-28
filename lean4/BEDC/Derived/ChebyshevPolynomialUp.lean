import BEDC.Derived.PolynomialUp.IntegerRing

namespace BEDC.Derived.ChebyshevPolynomialUp

abbrev IntegerUp := BEDC.Derived.PolynomialUp.IntegerUp
abbrev Poly := BEDC.Derived.PolynomialUp.Poly
abbrev PolyEq := BEDC.Derived.PolynomialUp.PolyEq

abbrev zZero : IntegerUp :=
  BEDC.Derived.RationalUp.intZero

abbrev zOne : IntegerUp :=
  BEDC.Derived.RationalUp.intOne

abbrev zTwo : IntegerUp :=
  BEDC.Derived.PolynomialUp.coeffOfNat 2

abbrev polyZero : Poly :=
  BEDC.Derived.PolynomialUp.polyZero

abbrev polyOne : Poly :=
  BEDC.Derived.PolynomialUp.polyOne

abbrev polyAdd : Poly -> Poly -> Poly :=
  BEDC.Derived.PolynomialUp.polyAdd

abbrev polyMul : Poly -> Poly -> Poly :=
  BEDC.Derived.PolynomialUp.polyMul

abbrev polyNeg : Poly -> Poly :=
  BEDC.Derived.PolynomialUp.polyNeg

abbrev polyScale : IntegerUp -> Poly -> Poly :=
  BEDC.Derived.PolynomialUp.polyScale

def polySub (p q : Poly) : Poly :=
  polyAdd p (polyNeg q)

def chebyshevX : Poly :=
  [zZero, zOne]

def chebyshevTwoX : Poly :=
  polyScale zTwo chebyshevX

def chebyshevT : Nat -> Poly
  | Nat.zero => polyOne
  | Nat.succ Nat.zero => chebyshevX
  | Nat.succ (Nat.succ n) =>
      polySub
        (polyMul chebyshevTwoX (chebyshevT (Nat.succ n)))
        (chebyshevT n)

def chebyshevU : Nat -> Poly
  | Nat.zero => polyOne
  | Nat.succ Nat.zero => chebyshevTwoX
  | Nat.succ (Nat.succ n) =>
      polySub
        (polyMul chebyshevTwoX (chebyshevU (Nat.succ n)))
        (chebyshevU n)

private abbrev polyLaws :=
  BEDC.Derived.PolynomialUp.polynomial_comm_ring_laws

private theorem PolyEq_refl (p : Poly) : PolyEq p p :=
  BEDC.Derived.PolynomialUp.PolyEq_refl p

private theorem PolyEq_symm {p q : Poly} :
    PolyEq p q -> PolyEq q p :=
  BEDC.Derived.PolynomialUp.PolyEq_symm

private theorem PolyEq_trans {p q r : Poly} :
    PolyEq p q -> PolyEq q r -> PolyEq p r :=
  BEDC.Derived.PolynomialUp.PolyEq_trans

private theorem polySub_respects {p p' q q' : Poly} :
    PolyEq p p' -> PolyEq q q' -> PolyEq (polySub p q) (polySub p' q') := by
  intro pp' qq'
  exact polyLaws.add_respects pp' (polyLaws.neg_respects qq')

private theorem polySub_add_cancel (p q : Poly) :
    PolyEq (polyAdd (polySub p q) q) p := by
  exact PolyEq_trans (polyLaws.add_assoc p (polyNeg q) q)
    (PolyEq_trans
      (polyLaws.add_respects (polyLaws.eq_refl p) (polyLaws.neg_add q))
      (polyLaws.add_zero p))

theorem chebyshevT_zero :
    chebyshevT 0 = polyOne := by
  rfl

theorem chebyshevT_one :
    chebyshevT 1 = chebyshevX := by
  rfl

theorem chebyshevT_recurrence (n : Nat) :
    chebyshevT (Nat.succ (Nat.succ n)) =
      polySub
        (polyMul chebyshevTwoX (chebyshevT (Nat.succ n)))
        (chebyshevT n) := by
  rfl

theorem chebyshevU_zero :
    chebyshevU 0 = polyOne := by
  rfl

theorem chebyshevU_one :
    chebyshevU 1 = chebyshevTwoX := by
  rfl

theorem chebyshevU_recurrence (n : Nat) :
    chebyshevU (Nat.succ (Nat.succ n)) =
      polySub
        (polyMul chebyshevTwoX (chebyshevU (Nat.succ n)))
        (chebyshevU n) := by
  rfl

theorem chebyshevT_neighbor_sum (n : Nat) :
    PolyEq
      (polyAdd (chebyshevT (Nat.succ (Nat.succ n))) (chebyshevT n))
      (polyMul chebyshevTwoX (chebyshevT (Nat.succ n))) := by
  exact polySub_add_cancel
    (polyMul chebyshevTwoX (chebyshevT (Nat.succ n)))
    (chebyshevT n)

theorem chebyshevU_neighbor_sum (n : Nat) :
    PolyEq
      (polyAdd (chebyshevU (Nat.succ (Nat.succ n))) (chebyshevU n))
      (polyMul chebyshevTwoX (chebyshevU (Nat.succ n))) := by
  exact polySub_add_cancel
    (polyMul chebyshevTwoX (chebyshevU (Nat.succ n)))
    (chebyshevU n)

theorem chebyshev_neighbor_sum_strong :
    ∀ n : Nat,
      PolyEq
          (polyAdd (chebyshevT (Nat.succ (Nat.succ n))) (chebyshevT n))
          (polyMul chebyshevTwoX (chebyshevT (Nat.succ n))) ∧
        PolyEq
          (polyAdd (chebyshevU (Nat.succ (Nat.succ n))) (chebyshevU n))
          (polyMul chebyshevTwoX (chebyshevU (Nat.succ n))) := by
  intro n
  exact Nat.strongRecOn n
    (fun k _previous =>
      And.intro (chebyshevT_neighbor_sum k) (chebyshevU_neighbor_sum k))

theorem chebyshevT_first_product_neighbor_sum (n : Nat) :
    PolyEq
      (polyScale zTwo (polyMul (chebyshevT 1) (chebyshevT (Nat.succ n))))
      (polyAdd (chebyshevT (Nat.succ (Nat.succ n))) (chebyshevT n)) := by
  have scaledProduct :
      PolyEq
        (polyScale zTwo (polyMul (chebyshevT 1) (chebyshevT (Nat.succ n))))
        (polyMul chebyshevTwoX (chebyshevT (Nat.succ n))) := by
    exact PolyEq_symm
      (BEDC.Derived.PolynomialUp.polyScale_mul_left
        zTwo chebyshevX (chebyshevT (Nat.succ n)))
  exact PolyEq_trans scaledProduct
    (PolyEq_symm (chebyshevT_neighbor_sum n))

theorem chebyshevT_two_square_relation :
    PolyEq (chebyshevT 2)
      (polySub
        (polyScale zTwo (polyMul (chebyshevT 1) (chebyshevT 1)))
        (chebyshevT 0)) := by
  exact polySub_respects
    (BEDC.Derived.PolynomialUp.polyScale_mul_left zTwo chebyshevX chebyshevX)
    (PolyEq_refl polyOne)

theorem chebyshevU_zero_eq_T_zero :
    PolyEq (chebyshevU 0) (chebyshevT 0) := by
  exact PolyEq_refl polyOne

theorem chebyshevU_one_eq_twoT_one :
    PolyEq (chebyshevU 1) (polyScale zTwo (chebyshevT 1)) := by
  exact PolyEq_refl chebyshevTwoX

theorem chebyshevT_two_unfolded :
    chebyshevT 2 =
      polySub (polyMul chebyshevTwoX chebyshevX) polyOne := by
  rfl

theorem chebyshevU_two_unfolded :
    chebyshevU 2 =
      polySub (polyMul chebyshevTwoX chebyshevTwoX) polyOne := by
  rfl

end BEDC.Derived.ChebyshevPolynomialUp
