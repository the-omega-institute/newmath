import BEDC.Derived.RHRoute.IntervalMatrixPSD.PolyPanelError

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

namespace BEDC.Derived.RHRoute.IntervalMatrixPSD

open BEDC.Algebra.Rel (RelCommRing)
open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumKernel

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

private theorem ratSub_respects {x x' y y' : BRat} :
    RatEq x x' -> RatEq y y' -> RatEq (ratSub x y) (ratSub x' y') := by
  intro hx hy
  unfold ratSub
  exact ratAdd_respects hx (ratNeg_respects hy)

private theorem ratSub_self_local (x : BRat) :
    RatEq (ratSub x x) ratZero :=
  BEDC.Derived.RationalUp.ratSub_self x

private theorem ratSub_add_cancel_left (x y : BRat) :
    RatEq (ratSub (ratAdd x y) x) y := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (BEDC.Derived.LocatedReal.ratAdd_assoc_local x y (ratNeg x))
    (RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl x) (ratAdd_comm y (ratNeg x)))
      (RatEq_trans _ _ _
        (RatEq_symm (BEDC.Derived.LocatedReal.ratAdd_assoc_local x (ratNeg x) y))
        (RatEq_trans _ _ _
          (ratAdd_respects (BEDC.Derived.LocatedReal.ratAdd_neg_local x)
            (RatEq_refl y))
          (ratZero_add_left y))))

private theorem ratSub_zero_left_neg (x : BRat) :
    RatEq (ratSub ratZero x) (ratNeg x) :=
  BEDC.Derived.LocatedReal.ratZero_sub_eq_neg x

private theorem ratNeg_nonneg_of_nonpos_local {x : BRat} :
    ratLe x ratZero -> ratLe ratZero (ratNeg x) := by
  intro h
  have subNonneg : ratLe ratZero (ratSub ratZero x) :=
    ratSub_nonneg_of_le h
  exact ratLe_respects (RatEq_refl _) (ratSub_zero_left_neg x) subNonneg

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

private theorem ratAbs_zero_local :
    RatEq (ratAbs ratZero) ratZero :=
  ratAbs_eq_self_of_nonneg_local (ratLe_refl ratZero)

private theorem ratAbs_sub_comm (x y : BRat) :
    RatEq (ratAbs (ratSub x y)) (ratAbs (ratSub y x)) := by
  exact RatEq_trans _ _ _
    (BEDC.Derived.LocatedReal.ratAbs_respects
      (BEDC.Derived.RationalUp.ratSub_swap_neg x y))
    (ratAbs_neg_local (ratSub y x))

private theorem ratAbs_neg_of_sub (x y : BRat) :
    RatEq (ratAbs (ratNeg (ratSub x y))) (ratAbs (ratSub x y)) :=
  ratAbs_neg_local (ratSub x y)

private theorem ratAdd_nonneg_local {x y : BRat} :
    ratLe ratZero x -> ratLe ratZero y -> ratLe ratZero (ratAdd x y) := by
  intro hx hy
  have raw : ratLe (ratAdd ratZero ratZero) (ratAdd x y) :=
    ratAdd_le_add hx hy
  exact ratLe_respects (ratZero_add_left ratZero) (RatEq_refl _) raw

private theorem ratLe_neg_anti_local {a b : BRat} :
    ratLe a b -> ratLe (ratNeg b) (ratNeg a) := by
  intro h
  let t := ratAdd (ratNeg a) (ratNeg b)
  have shifted : ratLe (ratAdd a t) (ratAdd b t) :=
    BEDC.Derived.LocatedReal.ratLe_add_right_mono
      (x := a) (x' := b) (y := t) h
  have leftEq : RatEq (ratAdd a t) (ratNeg b) := by
    unfold t
    exact RatEq_trans _ _ _
      (RatEq_symm
        (BEDC.Derived.LocatedReal.ratAdd_assoc_local a (ratNeg a) (ratNeg b)))
      (RatEq_trans _ _ _
        (ratAdd_respects (BEDC.Derived.LocatedReal.ratAdd_neg_local a)
          (RatEq_refl (ratNeg b)))
        (ratZero_add_left (ratNeg b)))
  have rightEq : RatEq (ratAdd b t) (ratNeg a) := by
    unfold t
    exact RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl b) (ratAdd_comm (ratNeg a) (ratNeg b)))
      (RatEq_trans _ _ _
        (RatEq_symm
          (BEDC.Derived.LocatedReal.ratAdd_assoc_local b (ratNeg b) (ratNeg a)))
        (RatEq_trans _ _ _
          (ratAdd_respects (BEDC.Derived.LocatedReal.ratAdd_neg_local b)
            (RatEq_refl (ratNeg a)))
          (ratZero_add_left (ratNeg a))))
  exact ratLe_respects leftEq rightEq shifted

private theorem ratAbs_le_of_between_max
    (a b z : BRat)
    (haz : ratLe a z)
    (hzb : ratLe z b) :
    ratLe (ratAbs z) (ratMax (ratAbs a) (ratAbs b)) := by
  cases ratLe_total ratZero z with
  | inl hzNonneg =>
      have zLeBound : ratLe z (ratMax (ratAbs a) (ratAbs b)) :=
        ratLe_trans hzb
          (ratLe_trans (BEDC.Derived.LocatedReal.ratLe_self_abs b)
            (ratMax_ge_right (ratAbs a) (ratAbs b)))
      exact ratAbs_le_of_nonneg_le hzNonneg zLeBound
  | inr hzNonpos =>
      have negZLeNegA : ratLe (ratNeg z) (ratNeg a) :=
        ratLe_neg_anti_local haz
      have negZLeBound : ratLe (ratNeg z) (ratMax (ratAbs a) (ratAbs b)) :=
        ratLe_trans negZLeNegA
          (ratLe_trans (BEDC.Derived.LocatedReal.ratLe_neg_abs a)
            (ratMax_ge_left (ratAbs a) (ratAbs b)))
      have absNegZLe :
          ratLe (ratAbs (ratNeg z)) (ratMax (ratAbs a) (ratAbs b)) :=
        ratAbs_le_of_nonneg_le (ratNeg_nonneg_of_nonpos_local hzNonpos)
          negZLeBound
      exact ratLe_respects (ratAbs_neg_local z) (RatEq_refl _) absNegZLe

def nsmulRat : Nat -> BRat -> BRat
  | 0, _h => ratZero
  | Nat.succ n, h => ratAdd (nsmulRat n h) h

theorem nsmulRat_succ (n : Nat) (h : BRat) :
    RatEq (nsmulRat (Nat.succ n) h) (ratAdd (nsmulRat n h) h) :=
  RatEq_refl _

theorem nsmulRat_nonneg (n : Nat) {h : BRat}
    (hh : ratLe ratZero h) :
    ratLe ratZero (nsmulRat n h) := by
  induction n with
  | zero =>
      change ratLe ratZero ratZero
      exact ratLe_refl ratZero
  | succ n ih =>
      change ratLe ratZero (ratAdd (nsmulRat n h) h)
      exact ratAdd_nonneg_local ih hh

private theorem ratNat_one_eq :
    RatEq (natRat 1) ratOne := by
  exact RatEq_refl _

private theorem natRat_succ_pos_local (n : Nat) :
    ratLt ratZero (natRat (Nat.succ n)) := by
  cases n with
  | zero =>
      change ratLt ratZero ratOne
      exact BEDC.Real.RatNumLogEnclosure.ratOne_pos
  | succ n =>
      cases n with
      | zero =>
          have oneKernel : RatEq ratOne (ratNat 1) := by
            unfold ratNat ratOne intToRat intOne intOfNat
            exact RatEq_refl _
          have h := BEDC.Real.RatNumLogEnclosure.ratNat_add 1 1
          have twoBridge : RatEq (natRat 2) (ratNat 2) := by
            change RatEq (ratAdd ratOne ratOne) (ratNat 2)
            exact RatEq_trans _ _ _
              (ratAdd_respects oneKernel oneKernel)
              h
          exact BEDC.Real.RatNumKernel.ratLt_of_RatEq_right
            (BEDC.Real.RatNumLogEnclosure.ratNat_pos_of_pos
              (Nat.succ_pos 1))
            (RatEq_symm twoBridge)
      | succ n =>
          change ratLt ratZero (ratNat (Nat.succ (Nat.succ (Nat.succ n))))
          exact BEDC.Real.RatNumLogEnclosure.ratNat_pos_of_pos
            (Nat.succ_pos _)

private theorem natRat_succ_apart_local (n : Nat) :
    ratApart0 (natRat (Nat.succ n)) :=
  ratApart0_of_pos (natRat_succ_pos_local n)

private theorem natRat_as_ratNat (n : Nat) :
    RatEq (natRat n) (ratNat n) := by
  cases n with
  | zero =>
      unfold natRat ratNat ratZero intToRat intZero intOfNat
      exact RatEq_refl _
  | succ n =>
      cases n with
      | zero =>
          unfold natRat
          unfold ratNat ratOne intToRat intOne intOfNat
          exact RatEq_refl _
      | succ n =>
          cases n with
          | zero =>
              have oneKernel : RatEq ratOne (ratNat 1) := by
                unfold ratNat ratOne intToRat intOne intOfNat
                exact RatEq_refl _
              change RatEq (ratAdd ratOne ratOne) (ratNat 2)
              exact RatEq_trans _ _ _
                (ratAdd_respects oneKernel oneKernel)
                (BEDC.Real.RatNumLogEnclosure.ratNat_add 1 1)
          | succ n =>
              change
                RatEq
                  (natRat (Nat.succ (Nat.succ (Nat.succ n))))
                  (ratNat (Nat.succ (Nat.succ (Nat.succ n))))
              exact RatEq_refl _

private theorem natRat_succ_local (n : Nat) :
    RatEq (natRat (Nat.succ n)) (ratAdd (natRat n) ratOne) := by
  have leftBridge : RatEq (natRat (Nat.succ n)) (ratNat (Nat.succ n)) :=
    natRat_as_ratNat (Nat.succ n)
  have addBridge :
      RatEq (ratAdd (natRat n) ratOne)
        (ratAdd (ratNat n) (ratNat 1)) := by
    exact ratAdd_respects (natRat_as_ratNat n) (RatEq_symm ratNat_one_eq)
  have kernelStep : RatEq (ratAdd (ratNat n) (ratNat 1)) (ratNat (Nat.succ n)) := by
    change RatEq (ratAdd (ratNat n) (ratNat 1)) (ratNat (n + 1))
    exact BEDC.Real.RatNumLogEnclosure.ratNat_add n 1
  exact RatEq_trans _ _ _ leftBridge
    (RatEq_symm (RatEq_trans _ _ _ addBridge kernelStep))

theorem nsmulRat_eq_natRat_mul (N : Nat) (h : BRat) :
    RatEq (nsmulRat N h) (ratMul (natRat N) h) := by
  induction N with
  | zero =>
      change RatEq ratZero (ratMul ratZero h)
      exact RatEq_symm (ratMul_zero_left_local h)
  | succ N ih =>
      change RatEq (ratAdd (nsmulRat N h) h)
        (ratMul (natRat (Nat.succ N)) h)
      have lhs :
          RatEq (ratAdd (nsmulRat N h) h)
            (ratAdd (ratMul (natRat N) h) (ratMul ratOne h)) :=
        ratAdd_respects ih (RatEq_symm (ratOne_mul_left h))
      have collect :
          RatEq (ratAdd (ratMul (natRat N) h) (ratMul ratOne h))
            (ratMul (ratAdd (natRat N) ratOne) h) :=
        RatEq_symm (BEDC.Real.RatNumKernel.ratMul_add_right (natRat N) ratOne h)
      have coeff :
          RatEq (ratMul (ratAdd (natRat N) ratOne) h)
            (ratMul (natRat (Nat.succ N)) h) :=
        ratMul_respects (RatEq_symm (natRat_succ_local N)) (RatEq_refl h)
      exact RatEq_trans _ _ _ lhs (RatEq_trans _ _ _ collect coeff)

def leftFrom (P : BRat -> BRat) (h : BRat) : Nat -> BRat -> BRat
  | 0, _x => ratZero
  | Nat.succ n, x => ratAdd (ratMul h (P x)) (leftFrom P h n (ratAdd x h))

def errFrom (P F : BRat -> BRat) (h : BRat) : Nat -> BRat -> BRat
  | 0, _x => ratZero
  | Nat.succ n, x =>
      ratAdd
        (ratSub (ratMul h (P x)) (ratSub (F (ratAdd x h)) (F x)))
        (errFrom P F h n (ratAdd x h))

private theorem endpoint_succ_eq (x h : BRat) (N : Nat) :
    RatEq (ratAdd x (nsmulRat (Nat.succ N) h))
      (ratAdd (ratAdd x h) (nsmulRat N h)) := by
  change RatEq (ratAdd x (ratAdd (nsmulRat N h) h))
    (ratAdd (ratAdd x h) (nsmulRat N h))
  exact RatEq_trans _ _ _
    (ratAdd_respects (RatEq_refl x) (ratAdd_comm (nsmulRat N h) h))
    (RatEq_symm
      (BEDC.Derived.LocatedReal.ratAdd_assoc_local x h (nsmulRat N h)))

private theorem ratSub_add_sub_cancel_middle (a c b : BRat) :
    RatEq (ratAdd (ratSub a c) (ratSub c b)) (ratSub a b) := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (BEDC.Derived.LocatedReal.ratAdd_assoc_local a (ratNeg c)
      (ratAdd c (ratNeg b)))
    (RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl a)
        (RatEq_symm
          (BEDC.Derived.LocatedReal.ratAdd_assoc_local
            (ratNeg c) c (ratNeg b))))
      (RatEq_trans _ _ _
        (ratAdd_respects (RatEq_refl a)
          (ratAdd_respects
            (BEDC.Derived.LocatedReal.ratNeg_add_local c)
            (RatEq_refl (ratNeg b))))
        (RatEq_trans _ _ _
          (ratAdd_respects (RatEq_refl a)
            (ratZero_add_left (ratNeg b)))
          (RatEq_refl (ratAdd a (ratNeg b))))))

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

private theorem left_step_algebra
    (A H T E Fx : BRat) :
    RatEq
      (ratSub (ratAdd H T) (ratSub A Fx))
      (ratAdd (ratSub H (ratSub E Fx)) (ratSub T (ratSub A E))) := by
  have middle :
      RatEq (ratAdd (ratSub E Fx) (ratSub A E)) (ratSub A Fx) :=
    RatEq_trans _ _ _
      (ratAdd_comm (ratSub E Fx) (ratSub A E))
      (ratSub_add_sub_cancel_middle A E Fx)
  have targetGrouped :
      RatEq
        (ratAdd (ratSub H (ratSub E Fx)) (ratSub T (ratSub A E)))
        (ratSub (ratAdd H T)
          (ratAdd (ratSub E Fx) (ratSub A E))) :=
    ratAdd_sub_add_sub H T (ratSub E Fx) (ratSub A E)
  exact RatEq_symm
    (RatEq_trans _ _ _ targetGrouped
      (ratSub_respects (RatEq_refl (ratAdd H T)) middle))

theorem leftFrom_minus_endpoint_eq_errFrom
    (P F : BRat -> BRat)
    (h : BRat)
    (hP : ∀ {x y : BRat}, RatEq x y -> RatEq (P x) (P y))
    (hF : ∀ {x y : BRat}, RatEq x y -> RatEq (F x) (F y)) :
    ∀ N x,
      RatEq
        (ratSub (leftFrom P h N x)
          (ratSub (F (ratAdd x (nsmulRat N h))) (F x)))
        (errFrom P F h N x)
  | 0, x => by
      change RatEq (ratSub ratZero (ratSub (F (ratAdd x ratZero)) (F x))) ratZero
      have endEq : RatEq (F (ratAdd x ratZero)) (F x) :=
        hF (ratAdd_zero_right x)
      have innerZero : RatEq (ratSub (F (ratAdd x ratZero)) (F x)) ratZero :=
        RatEq_trans _ _ _ (ratSub_respects endEq (RatEq_refl (F x)))
          (ratSub_self_local (F x))
      exact RatEq_trans _ _ _
        (ratSub_respects (RatEq_refl ratZero) innerZero)
        (RatEq_trans _ _ _ (ratSub_zero_left_neg ratZero)
          (BEDC.Derived.LocatedReal.ratNeg_add_local ratZero))
  | Nat.succ N, x => by
      change
        RatEq
          (ratSub
            (ratAdd (ratMul h (P x)) (leftFrom P h N (ratAdd x h)))
            (ratSub (F (ratAdd x (nsmulRat (Nat.succ N) h))) (F x)))
          (ratAdd
            (ratSub (ratMul h (P x))
              (ratSub (F (ratAdd x h)) (F x)))
            (errFrom P F h N (ratAdd x h)))
      let y := ratAdd x h
      let e := ratAdd y (nsmulRat N h)
      have endpointEq : RatEq (ratAdd x (nsmulRat (Nat.succ N) h)) e := by
        unfold e y
        exact endpoint_succ_eq x h N
      have FendpointEq :
          RatEq (F (ratAdd x (nsmulRat (Nat.succ N) h))) (F e) :=
        hF endpointEq
      have endpointReplace :
          RatEq
            (ratSub
              (ratAdd (ratMul h (P x)) (leftFrom P h N y))
              (ratSub (F (ratAdd x (nsmulRat (Nat.succ N) h))) (F x)))
            (ratSub
              (ratAdd (ratMul h (P x)) (leftFrom P h N y))
              (ratSub (F e) (F x))) :=
        ratSub_respects (RatEq_refl _)
          (ratSub_respects FendpointEq (RatEq_refl (F x)))
      have split :
          RatEq
            (ratSub
              (ratAdd (ratMul h (P x)) (leftFrom P h N y))
              (ratSub (F e) (F x)))
            (ratAdd
              (ratSub (ratMul h (P x))
                (ratSub (F y) (F x)))
              (ratSub (leftFrom P h N y) (ratSub (F e) (F y)))) :=
        left_step_algebra (F e) (ratMul h (P x)) (leftFrom P h N y) (F y) (F x)
      have ih := leftFrom_minus_endpoint_eq_errFrom P F h hP hF N y
      exact RatEq_trans _ _ _ endpointReplace
        (RatEq_trans _ _ _ split
          (ratAdd_respects (RatEq_refl _) ih))

inductive PanelsInBox (B h : BRat) : Nat -> BRat -> Prop where
  | zero (x : BRat) : PanelsInBox B h 0 x
  | succ (n : Nat) (x : BRat) :
      ratLe (ratAbs x) B ->
      ratLe (ratAbs (ratAdd x h)) B ->
      PanelsInBox B h n (ratAdd x h) ->
      PanelsInBox B h (Nat.succ n) x

private theorem ratDivTwo_nonneg {x : BRat}
    (hx : ratLe ratZero x) :
    ratLe ratZero (ratDivTwo x) := by
  unfold ratDivTwo
  exact BEDC.Real.RatNumKernel.ratDivApart_nonneg_of_nonneg_pos
    hx (natRat_succ_pos_local 1) (natRat_succ_apart_local 1)

private theorem pow_nonneg_local (z : BRat)
    (hz : ratLe ratZero z) :
    ∀ n : Nat, ratLe ratZero (pow z n) :=
  BEDC.Real.RatNumKernel.ratPow_nonneg hz

private theorem degWeight_nonneg (k : Nat) (B : BRat)
    (hB : ratLe ratZero B) :
    ratLe ratZero (degWeight k B) := by
  cases k with
  | zero =>
      change ratLe ratZero ratZero
      exact ratLe_refl ratZero
  | succ m =>
      change ratLe ratZero (ratMul (natRat (Nat.succ m)) (pow B m))
      exact BEDC.Real.RatNumKernel.ratMul_nonneg
        (ratLt_to_ratLe (natRat_succ_pos_local m))
        (pow_nonneg_local B hB m)

theorem derivBoundShift_nonneg (d : Nat) (cs : List BRat) (B : BRat)
    (hB : ratLe ratZero B) :
    ratLe ratZero (derivBoundShift d cs B) := by
  induction cs generalizing d with
  | nil =>
      change ratLe ratZero ratZero
      exact ratLe_refl ratZero
  | cons c cs ih =>
      change ratLe ratZero
        (ratAdd (ratMul (ratAbs c) (degWeight d B))
          (derivBoundShift (Nat.succ d) cs B))
      exact ratAdd_nonneg_local
        (BEDC.Real.RatNumKernel.ratMul_nonneg
          (ratMagnitude_nonneg c)
          (degWeight_nonneg d B hB))
        (ih (Nat.succ d))

theorem derivBound_nonneg (cs : List BRat) (B : BRat)
    (hB : ratLe ratZero B) :
    ratLe ratZero (derivBound cs B) := by
  unfold derivBound
  exact derivBoundShift_nonneg 0 cs B hB

private theorem rhsPanel_nonneg (cs : List BRat) (h B : BRat)
    (hh : ratLe ratZero h)
    (hB : ratLe ratZero B) :
    ratLe ratZero
      (ratDivTwo (ratMul (derivBound cs B) (ratMul h h))) := by
  exact ratDivTwo_nonneg
    (BEDC.Real.RatNumKernel.ratMul_nonneg
      (derivBound_nonneg cs B hB)
      (BEDC.Real.RatNumKernel.ratMul_nonneg hh hh))

private theorem natRat_nonneg_local (n : Nat) :
    ratLe ratZero (natRat n) := by
  exact BEDC.Real.RatNumKernel.ratLe_of_RatEq_right
    (BEDC.Real.RatNumKernel.ratNat_nonneg n)
    (RatEq_symm (natRat_as_ratNat n))

private theorem natRat_succ_mul (n : Nat) (C : BRat) :
    RatEq (ratMul (natRat (Nat.succ n)) C)
      (ratAdd (ratMul (natRat n) C) C) := by
  exact RatEq_trans _ _ _
    (ratMul_respects (natRat_succ_local n) (RatEq_refl C))
    (RatEq_trans _ _ _
      (BEDC.Real.RatNumKernel.ratMul_add_right (natRat n) ratOne C)
      (ratAdd_respects (RatEq_refl _) (ratOne_mul_left C)))

theorem errFrom_abs_bound
    (cs : List BRat) (h B : BRat)
    (hh : ratLe ratZero h)
    (hB : ratLe ratZero B) :
    ∀ N x, PanelsInBox B h N x ->
      ratLe (ratAbs (errFrom (evalPoly cs) (antiEvalPoly cs) h N x))
        (ratMul (natRat N)
          (ratDivTwo (ratMul (derivBound cs B) (ratMul h h)))) := by
  intro N x box
  induction box with
  | zero x =>
      change ratLe (ratAbs ratZero)
        (ratMul ratZero
          (ratDivTwo (ratMul (derivBound cs B) (ratMul h h))))
      exact ratLe_respects (RatEq_symm ratAbs_zero_local)
        (RatEq_symm (ratMul_zero_left_local _))
        (ratLe_refl ratZero)
  | succ n x hx hy _tailBox ih =>
      let C := ratDivTwo (ratMul (derivBound cs B) (ratMul h h))
      change
        ratLe
          (ratAbs
            (ratAdd
              (ratSub (ratMul h (evalPoly cs x))
                (ratSub (antiEvalPoly cs (ratAdd x h)) (antiEvalPoly cs x)))
              (errFrom (evalPoly cs) (antiEvalPoly cs) h n (ratAdd x h))))
          (ratMul (natRat (Nat.succ n)) C)
      have triangle :
          ratLe
            (ratAbs
              (ratAdd
                (ratSub (ratMul h (evalPoly cs x))
                  (ratSub (antiEvalPoly cs (ratAdd x h)) (antiEvalPoly cs x)))
                (errFrom (evalPoly cs) (antiEvalPoly cs) h n (ratAdd x h))))
            (ratAdd
              (ratAbs
                (ratSub (ratMul h (evalPoly cs x))
                  (ratSub (antiEvalPoly cs (ratAdd x h)) (antiEvalPoly cs x))))
              (ratAbs (errFrom (evalPoly cs) (antiEvalPoly cs) h n (ratAdd x h)))) :=
        BEDC.Derived.LocatedReal.ratAbs_triangle
          (ratSub (ratMul h (evalPoly cs x))
            (ratSub (antiEvalPoly cs (ratAdd x h)) (antiEvalPoly cs x)))
          (errFrom (evalPoly cs) (antiEvalPoly cs) h n (ratAdd x h))
      have headPoly :=
        poly_panel_error cs x h B hh hB hx hy
      have head :
          ratLe
            (ratAbs
              (ratSub (ratMul h (evalPoly cs x))
                (ratSub (antiEvalPoly cs (ratAdd x h)) (antiEvalPoly cs x))))
            C := by
        exact ratLe_respects
          (RatEq_symm
            (ratAbs_sub_comm (ratMul h (evalPoly cs x))
              (ratSub (antiEvalPoly cs (ratAdd x h)) (antiEvalPoly cs x))))
          (RatEq_refl C)
          headPoly
      have tail :
          ratLe
            (ratAbs (errFrom (evalPoly cs) (antiEvalPoly cs) h n (ratAdd x h)))
            (ratMul (natRat n) C) :=
        ih
      have added :
          ratLe
            (ratAdd
              (ratAbs
                (ratSub (ratMul h (evalPoly cs x))
                  (ratSub (antiEvalPoly cs (ratAdd x h)) (antiEvalPoly cs x))))
              (ratAbs (errFrom (evalPoly cs) (antiEvalPoly cs) h n (ratAdd x h))))
            (ratAdd C (ratMul (natRat n) C)) :=
        ratAdd_le_add head tail
      have rhsEq :
          RatEq (ratAdd C (ratMul (natRat n) C))
            (ratMul (natRat (Nat.succ n)) C) := by
        exact RatEq_trans _ _ _
          (ratAdd_comm C (ratMul (natRat n) C))
          (RatEq_symm (natRat_succ_mul n C))
      exact BEDC.Real.RatNumKernel.ratLe_of_RatEq_right
        (ratLe_trans triangle added) rhsEq

theorem left_sum_error_from
    (cs : List BRat) (h B : BRat)
    (hh : ratLe ratZero h)
    (hB : ratLe ratZero B)
    (N : Nat) (x : BRat)
    (box : PanelsInBox B h N x)
    (hEval : ∀ {u v : BRat}, RatEq u v -> RatEq (evalPoly cs u) (evalPoly cs v))
    (hAnti : ∀ {u v : BRat}, RatEq u v ->
      RatEq (antiEvalPoly cs u) (antiEvalPoly cs v)) :
    ratLe
      (ratAbs
        (ratSub (leftFrom (evalPoly cs) h N x)
          (ratSub (antiEvalPoly cs (ratAdd x (nsmulRat N h)))
            (antiEvalPoly cs x))))
      (ratMul (natRat N)
        (ratDivTwo (ratMul (derivBound cs B) (ratMul h h)))) := by
  have tel :=
    leftFrom_minus_endpoint_eq_errFrom
      (evalPoly cs) (antiEvalPoly cs) h hEval hAnti N x
  have bound := errFrom_abs_bound cs h B hh hB N x box
  exact BEDC.Real.RatNumKernel.ratLe_of_RatEq_left
    (BEDC.Derived.LocatedReal.ratAbs_respects tel)
    bound

private theorem pow_respects {x y : BRat}
    (hxy : RatEq x y) :
    ∀ n : Nat, RatEq (pow x n) (pow y n)
  | 0 => RatEq_refl ratOne
  | Nat.succ n => by
      change RatEq (ratMul (pow x n) x) (ratMul (pow y n) y)
      exact ratMul_respects (pow_respects hxy n) hxy

private theorem ratDivNat_respects {x y : BRat}
    (hxy : RatEq x y) (n : Nat) :
    RatEq (ratDivNat x n) (ratDivNat y n) := by
  unfold ratDivNat BEDC.Derived.RationalOrderArithUp.ratDivApart
  exact ratMul_respects hxy (RatEq_refl _)

private theorem evalShift_respects
    (d : Nat) (cs : List BRat) {x y : BRat}
    (hxy : RatEq x y) :
    RatEq (evalShift d cs x) (evalShift d cs y) := by
  induction cs generalizing d with
  | nil =>
      change RatEq ratZero ratZero
      exact RatEq_refl ratZero
  | cons c cs ih =>
      change
        RatEq
          (ratAdd (ratMul c (pow x d)) (evalShift (Nat.succ d) cs x))
          (ratAdd (ratMul c (pow y d)) (evalShift (Nat.succ d) cs y))
      exact ratAdd_respects
        (ratMul_respects (RatEq_refl c) (pow_respects hxy d))
        (ih (Nat.succ d))

private theorem antiEvalShift_respects
    (d : Nat) (cs : List BRat) {x y : BRat}
    (hxy : RatEq x y) :
    RatEq (antiEvalShift d cs x) (antiEvalShift d cs y) := by
  induction cs generalizing d with
  | nil =>
      change RatEq ratZero ratZero
      exact RatEq_refl ratZero
  | cons c cs ih =>
      change
        RatEq
          (ratAdd
            (ratDivNat (ratMul c (pow x (Nat.succ d))) d)
            (antiEvalShift (Nat.succ d) cs x))
          (ratAdd
            (ratDivNat (ratMul c (pow y (Nat.succ d))) d)
            (antiEvalShift (Nat.succ d) cs y))
      exact ratAdd_respects
        (ratDivNat_respects
          (ratMul_respects (RatEq_refl c) (pow_respects hxy (Nat.succ d))) d)
        (ih (Nat.succ d))

private theorem evalPoly_respects (cs : List BRat)
    {x y : BRat} :
    RatEq x y -> RatEq (evalPoly cs x) (evalPoly cs y) := by
  intro hxy
  unfold evalPoly
  exact evalShift_respects 0 cs hxy

private theorem antiEvalPoly_respects (cs : List BRat)
    {x y : BRat} :
    RatEq x y -> RatEq (antiEvalPoly cs x) (antiEvalPoly cs y) := by
  intro hxy
  unfold antiEvalPoly
  exact antiEvalShift_respects 0 cs hxy

def panels (n : Nat) : Nat :=
  Nat.succ n

def hUniform (a b : BRat) (n : Nat) : BRat :=
  ratDivNat (ratSub b a) n

theorem ratDivNat_mul_cancel (x : BRat) (n : Nat) :
    RatEq (ratMul (ratDivNat x n) (natRat (Nat.succ n))) x := by
  unfold ratDivNat
  exact BEDC.Real.RatNumKernel.ratDivApart_mul_cancel_right
    (natRat_succ_apart_local n)

private theorem ratDivNat_nonneg {x : BRat} (n : Nat)
    (hx : ratLe ratZero x) :
    ratLe ratZero (ratDivNat x n) := by
  unfold ratDivNat
  exact BEDC.Real.RatNumKernel.ratDivApart_nonneg_of_nonneg_pos
    hx (natRat_succ_pos_local n) (natRat_succ_apart_local n)

theorem hUniform_nonneg {a b : BRat} (n : Nat)
    (hab : ratLe a b) :
    ratLe ratZero (hUniform a b n) := by
  unfold hUniform
  exact ratDivNat_nonneg n (ratSub_nonneg_of_le hab)

private theorem ratAdd_sub_cancel_right (a b : BRat) :
    RatEq (ratAdd a (ratSub b a)) b := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (ratAdd_respects (RatEq_refl a) (ratAdd_comm b (ratNeg a)))
    (RatEq_trans _ _ _
      (RatEq_symm
        (BEDC.Derived.LocatedReal.ratAdd_assoc_local a (ratNeg a) b))
      (RatEq_trans _ _ _
        (ratAdd_respects (BEDC.Derived.LocatedReal.ratAdd_neg_local a)
          (RatEq_refl b))
        (ratZero_add_left b)))

private theorem uniform_endpoint (a b : BRat) (n : Nat) :
    RatEq (ratAdd a (nsmulRat (panels n) (hUniform a b n))) b := by
  unfold panels hUniform
  have nsmulEq :
      RatEq (nsmulRat (Nat.succ n) (ratDivNat (ratSub b a) n))
        (ratSub b a) := by
    exact RatEq_trans _ _ _
      (nsmulRat_eq_natRat_mul (Nat.succ n) (ratDivNat (ratSub b a) n))
      (RatEq_trans _ _ _
        (ratMul_comm (natRat (Nat.succ n)) (ratDivNat (ratSub b a) n))
        (ratDivNat_mul_cancel (ratSub b a) n))
  exact RatEq_trans _ _ _
    (ratAdd_respects (RatEq_refl a) nsmulEq)
    (ratAdd_sub_cancel_right a b)

private theorem ratLe_add_nonneg_right_local (x y : BRat)
    (hy : ratLe ratZero y) :
    ratLe x (ratAdd x y) := by
  have raw : ratLe (ratAdd x ratZero) (ratAdd x y) :=
    BEDC.Derived.LocatedReal.ratLe_add_left_mono
      (y := ratZero) (y' := y) (x := x) hy
  exact BEDC.Real.RatNumKernel.ratLe_of_RatEq_left
    (RatEq_symm (ratAdd_zero_right x)) raw

private theorem panelsInBox_segment
    (a b x h : BRat) (N : Nat)
    (hh : ratLe ratZero h)
    (hlo : ratLe a x)
    (hhi : ratLe x b)
    (hend : RatEq (ratAdd x (nsmulRat N h)) b) :
    PanelsInBox (ratMax (ratAbs a) (ratAbs b)) h N x := by
  induction N generalizing x with
  | zero =>
      exact PanelsInBox.zero x
  | succ n ih =>
      have hx : ratLe (ratAbs x) (ratMax (ratAbs a) (ratAbs b)) :=
        ratAbs_le_of_between_max a b x hlo hhi
      have xLeXh : ratLe x (ratAdd x h) :=
        ratLe_add_nonneg_right_local x h hh
      have hloNext : ratLe a (ratAdd x h) :=
        ratLe_trans hlo xLeXh
      have tailNonneg : ratLe ratZero (nsmulRat n h) :=
        nsmulRat_nonneg n hh
      have xhLeEnd :
          ratLe (ratAdd x h) (ratAdd (ratAdd x h) (nsmulRat n h)) :=
        ratLe_add_nonneg_right_local (ratAdd x h) (nsmulRat n h) tailNonneg
      have endNextEq :
          RatEq (ratAdd (ratAdd x h) (nsmulRat n h)) b := by
        exact RatEq_trans _ _ _
          (RatEq_symm (endpoint_succ_eq x h n))
          hend
      have hhiNext : ratLe (ratAdd x h) b :=
        BEDC.Real.RatNumKernel.ratLe_of_RatEq_right xhLeEnd endNextEq
      have hy : ratLe (ratAbs (ratAdd x h)) (ratMax (ratAbs a) (ratAbs b)) :=
        ratAbs_le_of_between_max a b (ratAdd x h) hloNext hhiNext
      exact PanelsInBox.succ n x hx hy
        (ih (ratAdd x h) hloNext hhiNext endNextEq)

private theorem uniform_box (a b : BRat) (hab : ratLe a b) (n : Nat) :
    PanelsInBox (ratMax (ratAbs a) (ratAbs b))
      (hUniform a b n) (panels n) a := by
  exact panelsInBox_segment a b a (hUniform a b n) (panels n)
    (hUniform_nonneg n hab)
    (ratLe_refl a)
    hab
    (uniform_endpoint a b n)

private theorem uniform_bound_nonneg (a b : BRat) :
    ratLe ratZero (ratMax (ratAbs a) (ratAbs b)) :=
  ratLe_trans (ratMagnitude_nonneg a) (ratMax_ge_left (ratAbs a) (ratAbs b))

theorem left_sum_error_uniform
    (cs : List BRat) (a b : BRat)
    (hab : ratLe a b) (n : Nat) :
    ratLe
      (ratAbs
        (ratSub
          (leftFrom (evalPoly cs) (hUniform a b n) (panels n) a)
          (ratSub (antiEvalPoly cs b) (antiEvalPoly cs a))))
      (ratMul (natRat (panels n))
        (ratDivTwo
          (ratMul
            (derivBound cs (ratMax (ratAbs a) (ratAbs b)))
            (ratMul (hUniform a b n) (hUniform a b n))))) := by
  let h := hUniform a b n
  let B := ratMax (ratAbs a) (ratAbs b)
  let N := panels n
  have hh : ratLe ratZero h := hUniform_nonneg n hab
  have hB : ratLe ratZero B := uniform_bound_nonneg a b
  have box : PanelsInBox B h N a := by
    unfold B h N
    exact uniform_box a b hab n
  have raw :=
    left_sum_error_from cs h B hh hB N a box
      (evalPoly_respects cs) (antiEvalPoly_respects cs)
  have endpointEq : RatEq (ratAdd a (nsmulRat N h)) b := by
    unfold N h
    exact uniform_endpoint a b n
  have antiEndpointEq :
      RatEq (antiEvalPoly cs (ratAdd a (nsmulRat N h)))
        (antiEvalPoly cs b) :=
    antiEvalPoly_respects cs endpointEq
  have insideEq :
      RatEq
        (ratSub (leftFrom (evalPoly cs) h N a)
          (ratSub (antiEvalPoly cs (ratAdd a (nsmulRat N h)))
            (antiEvalPoly cs a)))
        (ratSub (leftFrom (evalPoly cs) h N a)
          (ratSub (antiEvalPoly cs b) (antiEvalPoly cs a))) :=
    ratSub_respects (RatEq_refl _)
      (ratSub_respects antiEndpointEq (RatEq_refl _))
  exact BEDC.Real.RatNumKernel.ratLe_of_RatEq_left
    (RatEq_symm (BEDC.Derived.LocatedReal.ratAbs_respects insideEq))
    raw

end BEDC.Derived.RHRoute.IntervalMatrixPSD
