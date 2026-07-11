import BEDC.Derived.RHRoute.IntervalMatrixPSD.PanelError

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

namespace BEDC.Derived.RHRoute.IntervalMatrixPSD

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumKernel

def evalShift : Nat -> List BRat -> BRat -> BRat
  | _d, [], _x => ratZero
  | d, c :: cs, x =>
      ratAdd (ratMul c (pow x d)) (evalShift (Nat.succ d) cs x)

def antiEvalShift : Nat -> List BRat -> BRat -> BRat
  | _d, [], _x => ratZero
  | d, c :: cs, x =>
      ratAdd
        (ratDivNat (ratMul c (pow x (Nat.succ d))) d)
        (antiEvalShift (Nat.succ d) cs x)

def derivBoundShift : Nat -> List BRat -> BRat -> BRat
  | _d, [], _B => ratZero
  | d, c :: cs, B =>
      ratAdd (ratMul (ratAbs c) (degWeight d B))
        (derivBoundShift (Nat.succ d) cs B)

private def panelErrShift : Nat -> List BRat -> BRat -> BRat -> BRat
  | _d, [], _x, _h => ratZero
  | d, c :: cs, x, h =>
      ratAdd (ratMul c (monoPanelErr x h d))
        (panelErrShift (Nat.succ d) cs x h)

private theorem ratMul_zero_right_local (x : BRat) :
    RatEq (ratMul x ratZero) ratZero := by
  unfold RatEq ratMul ratZero intToRat
  change
    IntEq (IntMul (IntMul x.num intZero) (ratDenInt ratZero))
      (IntMul intZero (ratDenInt (ratMul x ratZero)))
  exact IntEq_trans (intMul_right_congr (intMul_zero_right x.num))
    (IntEq_symm (intMul_zero_left (ratDenInt (ratMul x ratZero))))

private theorem ratMul_zero_left_local (x : BRat) :
    RatEq (ratMul ratZero x) ratZero :=
  RatEq_trans _ _ _ (ratMul_comm ratZero x) (ratMul_zero_right_local x)

private theorem ratMul_neg_right_local (x y : BRat) :
    RatEq (ratMul x (ratNeg y)) (ratNeg (ratMul x y)) := by
  apply ratEq_of_num_den_intEq
  · unfold ratMul ratNeg
    exact BEDC.Algebra.Rel.IntegerUp_mul_neg x.num y.num
  · unfold ratMul ratNeg ratDenInt
    exact IntEq_refl _

private theorem ratSub_respects {x x' y y' : BRat} :
    RatEq x x' -> RatEq y y' -> RatEq (ratSub x y) (ratSub x' y') := by
  intro hx hy
  unfold ratSub
  exact ratAdd_respects hx (ratNeg_respects hy)

private theorem ratSub_mul_right (a b c : BRat) :
    RatEq (ratMul (ratSub a b) c)
      (ratSub (ratMul a c) (ratMul b c)) := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (BEDC.Real.RatNumKernel.ratMul_add_right a (ratNeg b) c)
    (ratAdd_respects (RatEq_refl (ratMul a c))
      (RatEq_trans _ _ _
        (ratMul_comm (ratNeg b) c)
        (RatEq_trans _ _ _
          (ratMul_neg_right_local c b)
          (ratNeg_respects (ratMul_comm c b)))))

private theorem ratSub_mul_left (c a b : BRat) :
    RatEq (ratMul c (ratSub a b))
      (ratSub (ratMul c a) (ratMul c b)) := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (BEDC.Real.RatNumKernel.ratMul_add_left c a (ratNeg b))
    (ratAdd_respects (RatEq_refl (ratMul c a))
      (ratMul_neg_right_local c b))

private theorem ratAdd_sub_add_sub (A U P Q : BRat) :
    RatEq (ratAdd (ratSub A P) (ratSub U Q))
      (ratSub (ratAdd A U) (ratAdd P Q)) := by
  unfold ratSub
  have regroup :
      RatEq
        (ratAdd (ratAdd A (ratNeg P)) (ratAdd U (ratNeg Q)))
        (ratAdd (ratAdd A U) (ratAdd (ratNeg P) (ratNeg Q))) := by
    exact RatEq_trans _ _ _
      (BEDC.Derived.LocatedReal.ratAdd_assoc_local A (ratNeg P)
        (ratAdd U (ratNeg Q)))
      (RatEq_trans _ _ _
        (ratAdd_respects (RatEq_refl A)
          (RatEq_trans _ _ _
            (RatEq_symm
              (BEDC.Derived.LocatedReal.ratAdd_assoc_local
                (ratNeg P) U (ratNeg Q)))
            (RatEq_trans _ _ _
              (ratAdd_respects (ratAdd_comm (ratNeg P) U)
                (RatEq_refl (ratNeg Q)))
              (BEDC.Derived.LocatedReal.ratAdd_assoc_local
                U (ratNeg P) (ratNeg Q)))))
        (RatEq_symm
          (BEDC.Derived.LocatedReal.ratAdd_assoc_local A U
            (ratAdd (ratNeg P) (ratNeg Q)))))
  exact RatEq_trans _ _ _ regroup
    (ratAdd_respects (RatEq_refl (ratAdd A U))
      (RatEq_symm (BEDC.Derived.LocatedReal.ratNeg_add_dist_local P Q)))

private theorem ratDivNat_mul_left (c a : BRat) (k : Nat) :
    RatEq (ratDivNat (ratMul c a) k) (ratMul c (ratDivNat a k)) := by
  unfold ratDivNat BEDC.Derived.RationalOrderArithUp.ratDivApart
  exact ratMul_assoc c a _

private theorem ratDivNat_sub (a b : BRat) (k : Nat) :
    RatEq (ratDivNat (ratSub a b) k)
      (ratSub (ratDivNat a k) (ratDivNat b k)) := by
  unfold ratDivNat BEDC.Derived.RationalOrderArithUp.ratDivApart
  exact ratSub_mul_right a b _

private theorem ratMul_rotate_head (h c p : BRat) :
    RatEq (ratMul h (ratMul c p)) (ratMul c (ratMul h p)) := by
  exact RatEq_trans _ _ _
    (RatEq_symm (ratMul_assoc h c p))
    (RatEq_trans _ _ _
      (ratMul_respects (ratMul_comm h c) (RatEq_refl p))
      (ratMul_assoc c h p))

private theorem head_panel_eq (c x h : BRat) (d : Nat) :
    RatEq
      (ratSub
        (ratSub
          (ratDivNat (ratMul c (pow (ratAdd x h) (Nat.succ d))) d)
          (ratDivNat (ratMul c (pow x (Nat.succ d))) d))
        (ratMul h (ratMul c (pow x d))))
      (ratMul c (monoPanelErr x h d)) := by
  have divLeft :
      RatEq
        (ratDivNat (ratMul c (pow (ratAdd x h) (Nat.succ d))) d)
        (ratMul c (ratDivNat (pow (ratAdd x h) (Nat.succ d)) d)) :=
    ratDivNat_mul_left c (pow (ratAdd x h) (Nat.succ d)) d
  have divRight :
      RatEq
        (ratDivNat (ratMul c (pow x (Nat.succ d))) d)
        (ratMul c (ratDivNat (pow x (Nat.succ d)) d)) :=
    ratDivNat_mul_left c (pow x (Nat.succ d)) d
  have diffScaled :
      RatEq
        (ratSub
          (ratDivNat (ratMul c (pow (ratAdd x h) (Nat.succ d))) d)
          (ratDivNat (ratMul c (pow x (Nat.succ d))) d))
        (ratMul c
          (ratSub
            (ratDivNat (pow (ratAdd x h) (Nat.succ d)) d)
            (ratDivNat (pow x (Nat.succ d)) d))) := by
    exact RatEq_trans _ _ _
      (ratSub_respects divLeft divRight)
      (RatEq_symm
        (ratSub_mul_left c
          (ratDivNat (pow (ratAdd x h) (Nat.succ d)) d)
          (ratDivNat (pow x (Nat.succ d)) d)))
  have divDiff :
      RatEq
        (ratSub
          (ratDivNat (pow (ratAdd x h) (Nat.succ d)) d)
          (ratDivNat (pow x (Nat.succ d)) d))
        (ratDivNat
          (ratSub (pow (ratAdd x h) (Nat.succ d))
            (pow x (Nat.succ d))) d) :=
    RatEq_symm
      (ratDivNat_sub (pow (ratAdd x h) (Nat.succ d))
        (pow x (Nat.succ d)) d)
  have first :
      RatEq
        (ratSub
          (ratSub
            (ratDivNat (ratMul c (pow (ratAdd x h) (Nat.succ d))) d)
            (ratDivNat (ratMul c (pow x (Nat.succ d))) d))
          (ratMul h (ratMul c (pow x d))))
        (ratSub
          (ratMul c
            (ratDivNat
              (ratSub (pow (ratAdd x h) (Nat.succ d))
                (pow x (Nat.succ d))) d))
          (ratMul c (ratMul h (pow x d)))) :=
    ratSub_respects
      (RatEq_trans _ _ _ diffScaled
        (ratMul_respects (RatEq_refl c) divDiff))
      (ratMul_rotate_head h c (pow x d))
  have collect :
      RatEq
        (ratSub
          (ratMul c
            (ratDivNat
              (ratSub (pow (ratAdd x h) (Nat.succ d))
                (pow x (Nat.succ d))) d))
          (ratMul c (ratMul h (pow x d))))
        (ratMul c (monoPanelErr x h d)) := by
    exact RatEq_symm
      (ratSub_mul_left c
        (ratDivNat
          (ratSub (pow (ratAdd x h) (Nat.succ d))
            (pow x (Nat.succ d))) d)
        (ratMul h (pow x d)))
  exact RatEq_trans _ _ _ first collect

private theorem panel_cons_split
    (A U P Q R S h : BRat) :
    RatEq
      (ratSub (ratSub (ratAdd A U) (ratAdd P Q))
        (ratMul h (ratAdd R S)))
      (ratAdd
        (ratSub (ratSub A P) (ratMul h R))
        (ratSub (ratSub U Q) (ratMul h S))) := by
  let X := ratSub A P
  let Y := ratSub U Q
  let HR := ratMul h R
  let HS := ratMul h S
  have diffSplit :
      RatEq (ratSub (ratAdd A U) (ratAdd P Q)) (ratAdd X Y) := by
    exact RatEq_symm (ratAdd_sub_add_sub A U P Q)
  have prodSplit :
      RatEq (ratMul h (ratAdd R S)) (ratAdd HR HS) := by
    exact BEDC.Real.RatNumKernel.ratMul_add_left h R S
  have grouped :
      RatEq
        (ratSub (ratSub (ratAdd A U) (ratAdd P Q))
          (ratMul h (ratAdd R S)))
        (ratSub (ratAdd X Y) (ratAdd HR HS)) :=
    ratSub_respects diffSplit prodSplit
  have ungrouped :
      RatEq (ratSub (ratAdd X Y) (ratAdd HR HS))
        (ratAdd (ratSub X HR) (ratSub Y HS)) :=
    RatEq_symm (ratAdd_sub_add_sub X Y HR HS)
  exact RatEq_trans _ _ _ grouped ungrouped

private theorem poly_panel_error_identity
    (d : Nat) (cs : List BRat) (x h : BRat) :
    RatEq
      (ratSub
        (ratSub (antiEvalShift d cs (ratAdd x h)) (antiEvalShift d cs x))
        (ratMul h (evalShift d cs x)))
      (panelErrShift d cs x h) := by
  induction cs generalizing d with
  | nil =>
      change RatEq (ratSub (ratSub ratZero ratZero) (ratMul h ratZero)) ratZero
      exact RatEq_trans _ _ _
        (ratSub_respects (ratSub_self ratZero) (ratMul_zero_right_local h))
        (ratSub_self ratZero)
  | cons c cs ih =>
      change
        RatEq
          (ratSub
            (ratSub
              (ratAdd
                (ratDivNat
                  (ratMul c (pow (ratAdd x h) (Nat.succ d))) d)
                (antiEvalShift (Nat.succ d) cs (ratAdd x h)))
              (ratAdd
                (ratDivNat (ratMul c (pow x (Nat.succ d))) d)
                (antiEvalShift (Nat.succ d) cs x)))
            (ratMul h
              (ratAdd (ratMul c (pow x d))
                (evalShift (Nat.succ d) cs x))))
          (ratAdd (ratMul c (monoPanelErr x h d))
            (panelErrShift (Nat.succ d) cs x h))
      have split :=
        panel_cons_split
          (ratDivNat (ratMul c (pow (ratAdd x h) (Nat.succ d))) d)
          (antiEvalShift (Nat.succ d) cs (ratAdd x h))
          (ratDivNat (ratMul c (pow x (Nat.succ d))) d)
          (antiEvalShift (Nat.succ d) cs x)
          (ratMul c (pow x d))
          (evalShift (Nat.succ d) cs x)
          h
      exact RatEq_trans _ _ _ split
        (ratAdd_respects (head_panel_eq c x h d) (ih (Nat.succ d)))

private theorem ratNeg_nonneg_of_nonpos_local {x : BRat} :
    ratLe x ratZero -> ratLe ratZero (ratNeg x) := by
  intro h
  have subNonneg : ratLe ratZero (ratSub ratZero x) :=
    ratSub_nonneg_of_le h
  exact ratLe_respects (RatEq_refl _) (BEDC.Derived.LocatedReal.ratZero_sub_eq_neg x)
    subNonneg

private theorem ratAbs_neg_local (x : BRat) :
    RatEq (ratAbs (ratNeg x)) (ratAbs x) := by
  unfold ratAbs
  exact ratMagnitude_neg x

private theorem ratAbs_eq_self_of_nonneg_local {x : BRat} :
    ratLe ratZero x -> RatEq (ratAbs x) x := by
  intro h
  unfold ratAbs
  exact ratMagnitude_eq_self_of_nonneg h

private theorem ratAbs_eq_neg_of_nonpos_local {x : BRat} :
    ratLe x ratZero -> RatEq (ratAbs x) (ratNeg x) := by
  intro h
  exact RatEq_trans _ _ _
    (RatEq_symm (ratAbs_neg_local x))
    (ratAbs_eq_self_of_nonneg_local (ratNeg_nonneg_of_nonpos_local h))

private theorem ratAbs_nonneg_left_mul_le {a x bound : BRat}
    (ha : ratLe ratZero a)
    (hx : ratLe (ratAbs x) bound) :
    ratLe (ratAbs (ratMul a x)) (ratMul a bound) := by
  cases ratLe_total ratZero x with
  | inl hxNonneg =>
      have axNonneg : ratLe ratZero (ratMul a x) :=
        ratMul_nonneg ha hxNonneg
      have absEq : RatEq (ratAbs (ratMul a x)) (ratMul a x) :=
        ratAbs_eq_self_of_nonneg_local axNonneg
      have xToAbs : ratLe x (ratAbs x) :=
        BEDC.Derived.LocatedReal.ratLe_self_abs x
      have xToBound : ratLe x bound := ratLe_trans xToAbs hx
      have raw : ratLe (ratMul a x) (ratMul a bound) :=
        ratMul_le_mul_left xToBound ha
      exact ratLe_respects (RatEq_symm absEq) (RatEq_refl _) raw
  | inr hxNonpos =>
      have prodNonpos : ratLe (ratMul a x) ratZero := by
        have raw : ratLe (ratMul a x) (ratMul a ratZero) :=
          ratMul_le_mul_left hxNonpos ha
        exact ratLe_respects (RatEq_refl _) (ratMul_zero_right_local a) raw
      have absEq : RatEq (ratAbs (ratMul a x)) (ratNeg (ratMul a x)) :=
        ratAbs_eq_neg_of_nonpos_local prodNonpos
      have negXToAbs : ratLe (ratNeg x) (ratAbs x) :=
        BEDC.Derived.LocatedReal.ratLe_neg_abs x
      have negXToBound : ratLe (ratNeg x) bound :=
        ratLe_trans negXToAbs hx
      have raw : ratLe (ratMul a (ratNeg x)) (ratMul a bound) :=
        ratMul_le_mul_left negXToBound ha
      have negProdEq : RatEq (ratMul a (ratNeg x)) (ratNeg (ratMul a x)) :=
        ratMul_neg_right_local a x
      exact ratLe_respects (RatEq_symm absEq) (RatEq_refl _)
        (ratLe_respects negProdEq (RatEq_refl _) raw)

private theorem ratAbs_nonneg_right_mul_le {x a bound : BRat}
    (ha : ratLe ratZero a)
    (hx : ratLe (ratAbs x) bound) :
    ratLe (ratAbs (ratMul x a)) (ratMul bound a) := by
  have left := ratAbs_nonneg_left_mul_le (a := a) (x := x) (bound := bound) ha hx
  exact ratLe_respects
    (BEDC.Derived.LocatedReal.ratAbs_respects (RatEq_symm (ratMul_comm x a)))
    (ratMul_comm a bound)
    left

private theorem ratAbs_mul_le {x y bx boundY : BRat}
    (hx : ratLe (ratAbs x) bx)
    (hy : ratLe (ratAbs y) boundY) :
    ratLe (ratAbs (ratMul x y)) (ratMul bx boundY) := by
  have bxNonneg : ratLe ratZero bx :=
    ratLe_trans (ratMagnitude_nonneg x) hx
  cases ratLe_total ratZero y with
  | inl yNonneg =>
      have first :
          ratLe (ratAbs (ratMul x y)) (ratMul bx y) :=
        ratAbs_nonneg_right_mul_le
          (a := y) (x := x) (bound := bx) yNonneg hx
      have yToBound : ratLe y boundY :=
        ratLe_trans (BEDC.Derived.LocatedReal.ratLe_self_abs y) hy
      have second :
          ratLe (ratMul bx y) (ratMul bx boundY) :=
        ratMul_le_mul_left yToBound bxNonneg
      exact ratLe_trans first second
  | inr yNonpos =>
      have negYNonneg : ratLe ratZero (ratNeg y) :=
        ratNeg_nonneg_of_nonpos_local yNonpos
      have first :
          ratLe (ratAbs (ratMul x (ratNeg y))) (ratMul bx (ratNeg y)) :=
        ratAbs_nonneg_right_mul_le
          (a := ratNeg y) (x := x) (bound := bx) negYNonneg hx
      have negYToBound : ratLe (ratNeg y) boundY :=
        ratLe_trans (BEDC.Derived.LocatedReal.ratLe_neg_abs y) hy
      have second :
          ratLe (ratMul bx (ratNeg y)) (ratMul bx boundY) :=
        ratMul_le_mul_left negYToBound bxNonneg
      have absBridge :
          RatEq (ratAbs (ratMul x (ratNeg y))) (ratAbs (ratMul x y)) := by
        exact RatEq_trans _ _ _
          (BEDC.Derived.LocatedReal.ratAbs_respects
            (ratMul_neg_right_local x y))
          (ratAbs_neg_local (ratMul x y))
      exact ratLe_respects absBridge (RatEq_refl _)
        (ratLe_trans first second)

private theorem ratDivTwo_respects {x y : BRat} :
    RatEq x y -> RatEq (ratDivTwo x) (ratDivTwo y) := by
  intro h
  unfold ratDivTwo BEDC.Derived.RationalOrderArithUp.ratDivApart
  exact ratMul_respects h (RatEq_refl _)

private theorem ratDivTwo_zero :
    RatEq (ratDivTwo ratZero) ratZero := by
  unfold ratDivTwo BEDC.Derived.RationalOrderArithUp.ratDivApart
  exact ratMul_zero_left_local _

private theorem ratDivTwo_add (a b : BRat) :
    RatEq (ratAdd (ratDivTwo a) (ratDivTwo b))
      (ratDivTwo (ratAdd a b)) := by
  unfold ratDivTwo BEDC.Derived.RationalOrderArithUp.ratDivApart
  exact RatEq_symm
    (BEDC.Real.RatNumKernel.ratMul_add_right a b
      _)

private theorem ratDivTwo_mul_left (a b : BRat) :
    RatEq (ratMul (ratDivTwo a) b) (ratDivTwo (ratMul a b)) := by
  unfold ratDivTwo BEDC.Derived.RationalOrderArithUp.ratDivApart
  exact RatEq_trans _ _ _
    (ratMul_assoc a (ratInvApart ratTwoPanel _) b)
    (RatEq_trans _ _ _
      (ratMul_respects (RatEq_refl a)
        (ratMul_comm (ratInvApart ratTwoPanel _) b))
      (RatEq_symm
        (ratMul_assoc a b
          (ratInvApart ratTwoPanel _))))

private theorem ratMul_divTwo_bound (a b q : BRat) :
    RatEq (ratMul a (ratDivTwo (ratMul b q)))
      (ratDivTwo (ratMul (ratMul a b) q)) := by
  have commute :
      RatEq (ratMul a (ratDivTwo (ratMul b q)))
        (ratMul (ratDivTwo (ratMul b q)) a) :=
    ratMul_comm a (ratDivTwo (ratMul b q))
  have moveHalf :
      RatEq (ratMul (ratDivTwo (ratMul b q)) a)
        (ratDivTwo (ratMul (ratMul b q) a)) :=
    ratDivTwo_mul_left (ratMul b q) a
  have reorder :
      RatEq (ratMul (ratMul b q) a) (ratMul (ratMul a b) q) := by
    exact RatEq_trans _ _ _
      (ratMul_assoc b q a)
      (RatEq_trans _ _ _
        (ratMul_respects (RatEq_refl b) (ratMul_comm q a))
        (RatEq_trans _ _ _
          (RatEq_symm (ratMul_assoc b a q))
          (ratMul_respects (ratMul_comm b a) (RatEq_refl q))))
  exact RatEq_trans _ _ _ commute
    (RatEq_trans _ _ _ moveHalf (ratDivTwo_respects reorder))

private theorem ratDivTwo_zero_product (q : BRat) :
    RatEq (ratDivTwo (ratMul ratZero q)) ratZero := by
  exact RatEq_trans _ _ _
    (ratDivTwo_respects (ratMul_zero_left_local q))
    ratDivTwo_zero

private theorem ratAbs_zero :
    RatEq (ratAbs ratZero) ratZero :=
  ratAbs_eq_self_of_nonneg_local (ratLe_refl ratZero)

private theorem panel_bound_rhs_cons
    (a dw tail q : BRat) :
    RatEq
      (ratAdd
        (ratDivTwo (ratMul (ratMul a dw) q))
        (ratDivTwo (ratMul tail q)))
      (ratDivTwo (ratMul (ratAdd (ratMul a dw) tail) q)) := by
  have halves :
      RatEq
        (ratAdd
          (ratDivTwo (ratMul (ratMul a dw) q))
          (ratDivTwo (ratMul tail q)))
        (ratDivTwo
          (ratAdd (ratMul (ratMul a dw) q) (ratMul tail q))) :=
    ratDivTwo_add (ratMul (ratMul a dw) q) (ratMul tail q)
  have collect :
      RatEq
        (ratAdd (ratMul (ratMul a dw) q) (ratMul tail q))
        (ratMul (ratAdd (ratMul a dw) tail) q) :=
    RatEq_symm
      (BEDC.Real.RatNumKernel.ratMul_add_right
        (ratMul a dw) tail q)
  exact RatEq_trans _ _ _ halves (ratDivTwo_respects collect)

private theorem poly_panel_error_shift_sum_bound
    (d : Nat) (cs : List BRat) (x h B : BRat)
    (hh : ratLe ratZero h)
    (hB : ratLe ratZero B)
    (hx : ratLe (ratAbs x) B)
    (hy : ratLe (ratAbs (ratAdd x h)) B) :
    ratLe (ratAbs (panelErrShift d cs x h))
      (ratDivTwo (ratMul (derivBoundShift d cs B) (ratMul h h))) := by
  induction cs generalizing d with
  | nil =>
      change
        ratLe (ratAbs ratZero)
          (ratDivTwo (ratMul ratZero (ratMul h h)))
      exact ratLe_respects (RatEq_symm ratAbs_zero)
        (RatEq_symm (ratDivTwo_zero_product (ratMul h h)))
        (ratLe_refl ratZero)
  | cons c cs ih =>
      change
        ratLe
          (ratAbs
            (ratAdd (ratMul c (monoPanelErr x h d))
              (panelErrShift (Nat.succ d) cs x h)))
          (ratDivTwo
            (ratMul
              (ratAdd (ratMul (ratAbs c) (degWeight d B))
                (derivBoundShift (Nat.succ d) cs B))
              (ratMul h h)))
      have triangle :
          ratLe
            (ratAbs
              (ratAdd (ratMul c (monoPanelErr x h d))
                (panelErrShift (Nat.succ d) cs x h)))
            (ratAdd
              (ratAbs (ratMul c (monoPanelErr x h d)))
              (ratAbs (panelErrShift (Nat.succ d) cs x h))) :=
        BEDC.Derived.LocatedReal.ratAbs_triangle
          (ratMul c (monoPanelErr x h d))
          (panelErrShift (Nat.succ d) cs x h)
      have monoBound :
          ratLe (ratAbs (monoPanelErr x h d))
            (ratDivTwo
              (ratMul (degWeight d B) (ratMul h h))) :=
        monomial_panel_error x h B hh hB hx hy d
      have headRaw :
          ratLe (ratAbs (ratMul c (monoPanelErr x h d)))
            (ratMul (ratAbs c)
              (ratDivTwo
                (ratMul (degWeight d B) (ratMul h h)))) :=
        ratAbs_mul_le (ratLe_refl (ratAbs c)) monoBound
      have headBound :
          ratLe (ratAbs (ratMul c (monoPanelErr x h d)))
            (ratDivTwo
              (ratMul (ratMul (ratAbs c) (degWeight d B))
                (ratMul h h))) :=
        BEDC.Real.RatNumKernel.ratLe_of_RatEq_right headRaw
          (ratMul_divTwo_bound (ratAbs c) (degWeight d B) (ratMul h h))
      have tailBound :
          ratLe (ratAbs (panelErrShift (Nat.succ d) cs x h))
            (ratDivTwo
              (ratMul (derivBoundShift (Nat.succ d) cs B)
                (ratMul h h))) :=
        ih (Nat.succ d)
      have added :
          ratLe
            (ratAdd
              (ratAbs (ratMul c (monoPanelErr x h d)))
              (ratAbs (panelErrShift (Nat.succ d) cs x h)))
            (ratAdd
              (ratDivTwo
                (ratMul (ratMul (ratAbs c) (degWeight d B))
                  (ratMul h h)))
              (ratDivTwo
                (ratMul (derivBoundShift (Nat.succ d) cs B)
                  (ratMul h h)))) :=
        ratAdd_le_add headBound tailBound
      exact BEDC.Real.RatNumKernel.ratLe_of_RatEq_right
        (ratLe_trans triangle added)
        (panel_bound_rhs_cons (ratAbs c) (degWeight d B)
          (derivBoundShift (Nat.succ d) cs B) (ratMul h h))

theorem poly_panel_error_shift
    (d : Nat) (cs : List BRat) (x h B : BRat)
    (hh : ratLe ratZero h)
    (hB : ratLe ratZero B)
    (hx : ratLe (ratAbs x) B)
    (hy : ratLe (ratAbs (ratAdd x h)) B) :
    ratLe
      (ratAbs
        (ratSub
          (ratSub (antiEvalShift d cs (ratAdd x h)) (antiEvalShift d cs x))
          (ratMul h (evalShift d cs x))))
      (ratDivTwo (ratMul (derivBoundShift d cs B) (ratMul h h))) := by
  have identity := poly_panel_error_identity d cs x h
  have bound :=
    poly_panel_error_shift_sum_bound d cs x h B hh hB hx hy
  exact BEDC.Real.RatNumKernel.ratLe_of_RatEq_left
    (BEDC.Derived.LocatedReal.ratAbs_respects identity)
    bound

def evalPoly (cs : List BRat) : BRat -> BRat :=
  evalShift 0 cs

def antiEvalPoly (cs : List BRat) : BRat -> BRat :=
  antiEvalShift 0 cs

def derivBound (cs : List BRat) : BRat -> BRat :=
  derivBoundShift 0 cs

theorem poly_panel_error
    (cs : List BRat) (x h B : BRat)
    (hh : ratLe ratZero h)
    (hB : ratLe ratZero B)
    (hx : ratLe (ratAbs x) B)
    (hy : ratLe (ratAbs (ratAdd x h)) B) :
    ratLe
      (ratAbs
        (ratSub
          (ratSub (antiEvalPoly cs (ratAdd x h)) (antiEvalPoly cs x))
          (ratMul h (evalPoly cs x))))
      (ratDivTwo (ratMul (derivBound cs B) (ratMul h h))) :=
  poly_panel_error_shift 0 cs x h B hh hB hx hy

end BEDC.Derived.RHRoute.IntervalMatrixPSD
