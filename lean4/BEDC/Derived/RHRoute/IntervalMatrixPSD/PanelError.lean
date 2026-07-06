import BEDC.Derived.RHRoute.IntervalMatrixPSD
import BEDC.Derived.LocatedReal.GroundedToleranceKit
import BEDC.Real.RatNumLogEnclosure

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

namespace BEDC.Derived.RHRoute.IntervalMatrixPSD

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumKernel
open BEDC.Real.RatNumLogEnclosure

def pow : BRat -> Nat -> BRat :=
  ratPow

def ratTwoPanel : BRat :=
  natRat 2

private theorem natRat_succ_pos (n : Nat) :
    ratLt ratZero (natRat (Nat.succ n)) := by
  cases n with
  | zero =>
      change ratLt ratZero ratOne
      exact ratOne_pos
  | succ n =>
      cases n with
      | zero =>
          have oneKernel : RatEq ratOne (ratNat 1) := by
            unfold ratNat ratOne intToRat intOne intOfNat
            exact RatEq_refl _
          have h := ratNat_add 1 1
          have twoBridge : RatEq (natRat 2) (ratNat 2) := by
            change RatEq (ratAdd ratOne ratOne) (ratNat 2)
            exact RatEq_trans _ _ _
              (ratAdd_respects oneKernel oneKernel)
              h
          exact BEDC.Real.RatNumKernel.ratLt_of_RatEq_right
            (ratNat_pos_of_pos (Nat.succ_pos 1))
            (RatEq_symm twoBridge)
      | succ n =>
          change ratLt ratZero (ratNat (Nat.succ (Nat.succ (Nat.succ n))))
          exact ratNat_pos_of_pos (Nat.succ_pos _)

private theorem natRat_succ_apart (n : Nat) :
    ratApart0 (natRat (Nat.succ n)) :=
  ratApart0_of_pos (natRat_succ_pos n)

def ratDivNat (x : BRat) (n : Nat) : BRat :=
  ratDivApart x (natRat (Nat.succ n))
    (natRat_succ_apart n)

def ratDivTwo (x : BRat) : BRat :=
  ratDivApart x ratTwoPanel (natRat_succ_apart 1)

def degWeight (k : Nat) (B : BRat) : BRat :=
  match k with
  | 0 => ratZero
  | Nat.succ m => ratMul (natRat (Nat.succ m)) (pow B m)

def diffQuot (x y : BRat) : Nat -> BRat
  | 0 => ratZero
  | Nat.succ n => ratAdd (pow y n) (ratMul x (diffQuot x y n))

def avgErrNum (x y : BRat) (k : Nat) : BRat :=
  ratSub (diffQuot x y (Nat.succ k))
    (ratMul (natRat (Nat.succ k)) (pow x k))

def triRat : Nat -> BRat
  | 0 => ratZero
  | Nat.succ n => ratAdd (triRat n) (natRat (Nat.succ n))

def monoPanelErr (x h : BRat) (k : Nat) : BRat :=
  ratSub
    (ratDivNat (ratSub (pow (ratAdd x h) (Nat.succ k)) (pow x (Nat.succ k))) k)
    (ratMul h (pow x k))

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

private theorem ratNat_one_eq :
    RatEq (natRat 1) ratOne := by
  exact RatEq_refl _

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
                (ratNat_add 1 1)
          | succ n =>
              change
                RatEq
                  (natRat (Nat.succ (Nat.succ (Nat.succ n))))
                  (ratNat (Nat.succ (Nat.succ (Nat.succ n))))
              exact RatEq_refl _

private theorem ratNat_succ (n : Nat) :
    RatEq (natRat (Nat.succ n)) (ratAdd (natRat n) ratOne) := by
  have leftBridge : RatEq (natRat (Nat.succ n)) (ratNat (Nat.succ n)) :=
    natRat_as_ratNat (Nat.succ n)
  have addBridge :
      RatEq (ratAdd (natRat n) ratOne)
        (ratAdd (ratNat n) (ratNat 1)) := by
    exact ratAdd_respects (natRat_as_ratNat n) (RatEq_symm ratNat_one_eq)
  have kernelStep : RatEq (ratAdd (ratNat n) (ratNat 1)) (ratNat (Nat.succ n)) := by
    change RatEq (ratAdd (ratNat n) (ratNat 1)) (ratNat (n + 1))
    exact ratNat_add n 1
  exact RatEq_trans _ _ _ leftBridge
    (RatEq_symm (RatEq_trans _ _ _ addBridge kernelStep))

private theorem ratSub_self (x : BRat) :
    RatEq (ratSub x x) ratZero := by
  unfold ratSub
  exact BEDC.Derived.LocatedReal.ratAdd_neg_local x

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
          (ratAdd_respects (BEDC.Derived.LocatedReal.ratAdd_neg_local x) (RatEq_refl y))
          (ratZero_add_left y))))

private theorem ratSub_respects {x x' y y' : BRat} :
    RatEq x x' -> RatEq y y' -> RatEq (ratSub x y) (ratSub x' y') := by
  intro hx hy
  unfold ratSub
  exact ratAdd_respects hx (ratNeg_respects hy)

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

private theorem ratMul_assoc_swap_last (a b c : BRat) :
    RatEq (ratMul (ratMul a b) c) (ratMul a (ratMul c b)) := by
  exact RatEq_trans _ _ _
    (ratMul_assoc a b c)
    (ratMul_respects (RatEq_refl a) (ratMul_comm b c))

theorem pow_sub_pow_eq_mul_diffQuot (x y : BRat) :
    ∀ n : Nat,
      RatEq (ratSub (pow y n) (pow x n))
        (ratMul (ratSub y x) (diffQuot x y n))
  | 0 => by
      change RatEq (ratSub ratOne ratOne) (ratMul (ratSub y x) ratZero)
      exact RatEq_trans _ _ _
        (ratSub_self ratOne)
        (RatEq_symm (ratMul_zero_right_local (ratSub y x)))
  | Nat.succ n => by
      let a := pow y n
      let b := pow x n
      let d := diffQuot x y n
      have ih :
          RatEq (ratSub a b) (ratMul (ratSub y x) d) := by
        unfold a b d
        exact pow_sub_pow_eq_mul_diffQuot x y n
      change
        RatEq (ratSub (ratMul a y) (ratMul b x))
          (ratMul (ratSub y x) (ratAdd a (ratMul x d)))
      have split :
          RatEq (ratSub (ratMul a y) (ratMul b x))
            (ratAdd
              (ratSub (ratMul a y) (ratMul a x))
              (ratSub (ratMul a x) (ratMul b x))) := by
        exact RatEq_symm
          (ratSub_add_sub_cancel_middle
            (ratMul a y) (ratMul a x) (ratMul b x))
      have first :
          RatEq (ratSub (ratMul a y) (ratMul a x))
            (ratMul (ratSub y x) a) := by
        exact RatEq_trans _ _ _
          (RatEq_symm (ratSub_mul_left a y x))
          (ratMul_comm a (ratSub y x))
      have second :
          RatEq (ratSub (ratMul a x) (ratMul b x))
            (ratMul (ratSub y x) (ratMul x d)) := by
        exact RatEq_trans _ _ _
          (RatEq_symm (ratSub_mul_right a b x))
          (RatEq_trans _ _ _
            (ratMul_respects ih (RatEq_refl x))
            (ratMul_assoc_swap_last (ratSub y x) d x))
      have distributed :
          RatEq
            (ratAdd (ratMul (ratSub y x) a)
              (ratMul (ratSub y x) (ratMul x d)))
            (ratMul (ratSub y x) (ratAdd a (ratMul x d))) := by
        exact RatEq_symm
          (BEDC.Real.RatNumKernel.ratMul_add_left
            (ratSub y x) a (ratMul x d))
      exact RatEq_trans _ _ _ split
        (RatEq_trans _ _ _
          (ratAdd_respects first second)
          distributed)

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

theorem abs_pow_le
    (z B : BRat)
    (hB : ratLe ratZero B)
    (hz : ratLe (ratAbs z) B) :
    ∀ n : Nat, ratLe (ratAbs (pow z n)) (pow B n)
  | 0 => by
      change ratLe (ratAbs ratOne) ratOne
      exact ratLe_of_RatEq_left
        (RatEq_symm (ratAbs_eq_self_of_nonneg_local ratOne_nonneg))
        (ratLe_refl ratOne)
  | Nat.succ n => by
      change ratLe (ratAbs (ratMul (pow z n) z)) (ratMul (pow B n) B)
      exact ratAbs_mul_le (abs_pow_le z B hB hz n) hz

private theorem ratMul_scalar_step (B c p : BRat) :
    RatEq (ratMul B (ratMul c p)) (ratMul c (ratMul p B)) := by
  exact RatEq_trans _ _ _
    (RatEq_symm (ratMul_assoc B c p))
    (RatEq_trans _ _ _
      (ratMul_respects (ratMul_comm B c) (RatEq_refl p))
      (RatEq_trans _ _ _
        (ratMul_assoc c B p)
        (ratMul_respects (RatEq_refl c) (ratMul_comm B p))))

private theorem ratAdd_mul_succ_coeff (c p : BRat) :
    RatEq (ratAdd p (ratMul c p)) (ratMul (ratAdd c ratOne) p) := by
  have expand :
      RatEq (ratMul (ratAdd c ratOne) p)
        (ratAdd (ratMul c p) (ratMul ratOne p)) :=
    BEDC.Real.RatNumKernel.ratMul_add_right c ratOne p
  exact RatEq_trans _ _ _
    (ratAdd_comm p (ratMul c p))
    (RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl (ratMul c p))
        (RatEq_symm (ratOne_mul_left p)))
      (RatEq_symm expand))

private theorem diffQuot_bound_step_alg (B : BRat) (n : Nat) :
    RatEq
      (ratAdd (pow B (Nat.succ n))
        (ratMul B (ratMul (natRat (Nat.succ n)) (pow B n))))
      (ratMul (natRat (Nat.succ (Nat.succ n))) (pow B (Nat.succ n))) := by
  let c := natRat (Nat.succ n)
  let p := pow B n
  let q := pow B (Nat.succ n)
  have qEq : RatEq q (ratMul p B) := by
    unfold q p pow
    exact RatEq_refl _
  have scaled :
      RatEq (ratMul B (ratMul c p)) (ratMul c q) := by
    exact RatEq_trans _ _ _
      (ratMul_scalar_step B c p)
      (ratMul_respects (RatEq_refl c) (RatEq_symm qEq))
  have addStep :
      RatEq (ratAdd q (ratMul c q))
        (ratMul (natRat (Nat.succ (Nat.succ n))) q) := by
    exact RatEq_trans _ _ _
      (ratAdd_mul_succ_coeff c q)
      (ratMul_respects (RatEq_symm (ratNat_succ (Nat.succ n)))
        (RatEq_refl q))
  exact RatEq_trans _ _ _
    (ratAdd_respects (RatEq_refl q) scaled)
    (RatEq_trans _ _ _ addStep
      (ratMul_respects (RatEq_refl (natRat (Nat.succ (Nat.succ n)))) qEq))

theorem diffQuot_abs_bound_succ
    (x y B : BRat)
    (hB : ratLe ratZero B)
    (hx : ratLe (ratAbs x) B)
    (hy : ratLe (ratAbs y) B) :
    ∀ n : Nat,
      ratLe (ratAbs (diffQuot x y (Nat.succ n)))
        (ratMul (natRat (Nat.succ n)) (pow B n))
  | 0 => by
      change
        ratLe (ratAbs (ratAdd ratOne (ratMul x ratZero)))
          (ratMul ratOne ratOne)
      have leftEq :
          RatEq (ratAbs (ratAdd ratOne (ratMul x ratZero))) ratOne := by
        exact RatEq_trans _ _ _
          (BEDC.Derived.LocatedReal.ratAbs_respects
            (RatEq_trans _ _ _
              (ratAdd_respects (RatEq_refl ratOne)
                (ratMul_zero_right_local x))
              (ratAdd_zero_right ratOne)))
          (ratAbs_eq_self_of_nonneg_local ratOne_nonneg)
      have rightEq : RatEq (ratMul ratOne ratOne) ratOne :=
        ratOne_mul_left ratOne
      exact ratLe_respects (RatEq_symm leftEq) (RatEq_symm rightEq)
        (ratLe_refl ratOne)
  | Nat.succ n => by
      change
        ratLe
          (ratAbs
            (ratAdd (pow y (Nat.succ n))
              (ratMul x (diffQuot x y (Nat.succ n)))))
          (ratMul (natRat (Nat.succ (Nat.succ n))) (pow B (Nat.succ n)))
      have triangle :
          ratLe
            (ratAbs
              (ratAdd (pow y (Nat.succ n))
                (ratMul x (diffQuot x y (Nat.succ n)))))
            (ratAdd (ratAbs (pow y (Nat.succ n)))
              (ratAbs (ratMul x (diffQuot x y (Nat.succ n))))) :=
        BEDC.Derived.LocatedReal.ratAbs_triangle
          (pow y (Nat.succ n))
          (ratMul x (diffQuot x y (Nat.succ n)))
      have powBound :
          ratLe (ratAbs (pow y (Nat.succ n))) (pow B (Nat.succ n)) :=
        abs_pow_le y B hB hy (Nat.succ n)
      have prodBound :
          ratLe (ratAbs (ratMul x (diffQuot x y (Nat.succ n))))
            (ratMul B (ratMul (natRat (Nat.succ n)) (pow B n))) :=
        ratAbs_mul_le hx
          (diffQuot_abs_bound_succ x y B hB hx hy n)
      have added :
          ratLe
            (ratAdd (ratAbs (pow y (Nat.succ n)))
              (ratAbs (ratMul x (diffQuot x y (Nat.succ n)))))
            (ratAdd (pow B (Nat.succ n))
              (ratMul B (ratMul (natRat (Nat.succ n)) (pow B n)))) :=
        ratAdd_le_add powBound prodBound
      exact ratLe_of_RatEq_right
        (ratLe_trans triangle added)
        (diffQuot_bound_step_alg B n)

private theorem ratPow_succ_coeff_bridge (x c : BRat) (k : Nat) :
    RatEq (ratMul x (ratMul c (pow x k)))
      (ratMul c (pow x (Nat.succ k))) := by
  have step := ratMul_scalar_step x c (pow x k)
  change RatEq (ratMul x (ratMul c (pow x k)))
    (ratMul c (ratMul (pow x k) x))
  exact step

theorem avgErrNum_succ (x y : BRat) :
    ∀ k : Nat,
      RatEq (avgErrNum x y (Nat.succ k))
        (ratAdd
          (ratSub (pow y (Nat.succ k)) (pow x (Nat.succ k)))
          (ratMul x (avgErrNum x y k)))
  | k => by
      let A := pow y (Nat.succ k)
      let P := pow x (Nat.succ k)
      let D := diffQuot x y (Nat.succ k)
      let C := natRat (Nat.succ k)
      let Cnext := natRat (Nat.succ (Nat.succ k))
      change
        RatEq (ratSub (ratAdd A (ratMul x D)) (ratMul Cnext P))
          (ratAdd (ratSub A P)
            (ratMul x (ratSub D (ratMul C (pow x k)))))
      have xAvg :
          RatEq (ratMul x (ratSub D (ratMul C (pow x k))))
            (ratSub (ratMul x D) (ratMul C P)) := by
        exact RatEq_trans _ _ _
          (ratSub_mul_left x D (ratMul C (pow x k)))
          (ratSub_respects (RatEq_refl (ratMul x D))
            (ratPow_succ_coeff_bridge x C k))
      have rhsToGrouped :
          RatEq
            (ratAdd (ratSub A P)
              (ratMul x (ratSub D (ratMul C (pow x k)))))
            (ratSub (ratAdd A (ratMul x D))
              (ratAdd P (ratMul C P))) := by
        exact RatEq_trans _ _ _
          (ratAdd_respects (RatEq_refl (ratSub A P)) xAvg)
          (ratAdd_sub_add_sub A (ratMul x D) P (ratMul C P))
      have coeff :
          RatEq (ratAdd P (ratMul C P)) (ratMul Cnext P) := by
        exact RatEq_trans _ _ _
          (ratAdd_mul_succ_coeff C P)
          (ratMul_respects (RatEq_symm (ratNat_succ (Nat.succ k)))
            (RatEq_refl P))
      have groupedToLhs :
          RatEq
            (ratSub (ratAdd A (ratMul x D))
              (ratAdd P (ratMul C P)))
            (ratSub (ratAdd A (ratMul x D)) (ratMul Cnext P)) :=
        ratSub_respects (RatEq_refl _) coeff
      exact RatEq_symm
        (RatEq_trans _ _ _ rhsToGrouped groupedToLhs)

private theorem avgErr_zero (x y : BRat) :
    RatEq (avgErrNum x y 0) ratZero := by
  change RatEq (ratSub (ratAdd ratOne (ratMul x ratZero)) ratOne) ratZero
  exact RatEq_trans _ _ _
    (ratSub_respects
      (RatEq_trans _ _ _
        (ratAdd_respects (RatEq_refl ratOne) (ratMul_zero_right_local x))
        (ratAdd_zero_right ratOne))
      (RatEq_refl ratOne))
    (ratSub_self ratOne)

private theorem avg_bound_step_alg (B h : BRat) (m : Nat) :
    RatEq
      (ratAdd
        (ratMul (ratMul (natRat (Nat.succ (Nat.succ m))) (pow B (Nat.succ m))) h)
        (ratMul B
          (ratMul (ratMul (triRat (Nat.succ m)) (pow B m)) h)))
      (ratMul (ratMul (triRat (Nat.succ (Nat.succ m))) (pow B (Nat.succ m))) h) := by
  let ncoef := natRat (Nat.succ (Nat.succ m))
  let tcoef := triRat (Nat.succ m)
  let p := pow B m
  let q := pow B (Nat.succ m)
  have qEq : RatEq q (ratMul p B) := by
    unfold q p pow
    exact RatEq_refl _
  have first :
      RatEq (ratMul (ratMul ncoef q) h)
        (ratMul ncoef (ratMul q h)) :=
    ratMul_assoc ncoef q h
  have second :
      RatEq (ratMul B (ratMul (ratMul tcoef p) h))
        (ratMul tcoef (ratMul q h)) := by
    exact RatEq_trans _ _ _
      (RatEq_symm (ratMul_assoc B (ratMul tcoef p) h))
      (RatEq_trans _ _ _
        (ratMul_respects
          (RatEq_trans _ _ _
            (ratMul_comm B (ratMul tcoef p))
            (RatEq_trans _ _ _
              (ratMul_assoc tcoef p B)
              (ratMul_respects (RatEq_refl tcoef) (RatEq_symm qEq))))
          (RatEq_refl h))
        (ratMul_assoc tcoef q h))
  have sumCoeff :
      RatEq
        (ratAdd (ratMul ncoef (ratMul q h))
          (ratMul tcoef (ratMul q h)))
        (ratMul (ratAdd ncoef tcoef) (ratMul q h)) := by
    exact RatEq_symm
      (BEDC.Real.RatNumKernel.ratMul_add_right ncoef tcoef (ratMul q h))
  have coeffComm :
      RatEq (ratAdd ncoef tcoef) (triRat (Nat.succ (Nat.succ m))) := by
    change RatEq
      (ratAdd (natRat (Nat.succ (Nat.succ m))) (triRat (Nat.succ m)))
      (ratAdd (triRat (Nat.succ m)) (natRat (Nat.succ (Nat.succ m))))
    exact ratAdd_comm _ _
  exact RatEq_trans _ _ _
    (ratAdd_respects first second)
    (RatEq_trans _ _ _ sumCoeff
      (RatEq_trans _ _ _
        (ratMul_respects coeffComm (RatEq_refl (ratMul q h)))
        (RatEq_symm
          (ratMul_assoc
            (triRat (Nat.succ (Nat.succ m))) q h))))

private theorem avgErrNum_abs_bound_pos_zero
    (x h B : BRat)
    (hh : ratLe ratZero h) :
    ratLe (ratAbs (avgErrNum x (ratAdd x h) 1))
      (ratMul (ratMul (triRat 1) (pow B 0)) h) := by
  change
    ratLe (ratAbs (avgErrNum x (ratAdd x h) 1))
      (ratMul (ratMul (triRat 1) ratOne) h)
  have recStep := avgErrNum_succ x (ratAdd x h) 0
  have diffEq :
      RatEq (ratSub (pow (ratAdd x h) 1) (pow x 1)) h := by
    change RatEq
      (ratSub (ratMul ratOne (ratAdd x h)) (ratMul ratOne x)) h
    exact RatEq_trans _ _ _
      (ratSub_respects (ratOne_mul_left (ratAdd x h)) (ratOne_mul_left x))
      (ratSub_add_cancel_left x h)
  have recEq :
      RatEq (avgErrNum x (ratAdd x h) 1) h := by
    exact RatEq_trans _ _ _ recStep
      (RatEq_trans _ _ _
        (ratAdd_respects diffEq
          (RatEq_trans _ _ _
            (ratMul_respects (RatEq_refl x) (avgErr_zero x (ratAdd x h)))
            (ratMul_zero_right_local x)))
        (ratAdd_zero_right h))
  have rhsEq :
      RatEq (ratMul (ratMul (triRat 1) ratOne) h) h := by
    change RatEq (ratMul (ratMul (ratAdd ratZero ratOne) ratOne) h) h
    exact RatEq_trans _ _ _
      (ratMul_respects
        (RatEq_trans _ _ _
          (ratMul_respects (ratZero_add_left ratOne) (RatEq_refl ratOne))
          (ratOne_mul_left ratOne))
        (RatEq_refl h))
      (ratOne_mul_left h)
  exact ratLe_of_RatEq_right
    (ratLe_of_RatEq_left
      (RatEq_trans _ _ _
        (BEDC.Derived.LocatedReal.ratAbs_respects recEq)
        (ratAbs_eq_self_of_nonneg_local hh))
    (ratLe_refl h))
    (RatEq_symm rhsEq)

private theorem avg_pow_diff_bound
    (x h B : BRat)
    (hh : ratLe ratZero h)
    (hB : ratLe ratZero B)
    (hx : ratLe (ratAbs x) B)
    (hy : ratLe (ratAbs (ratAdd x h)) B)
    (m : Nat) :
    ratLe
      (ratAbs (ratSub (pow (ratAdd x h) (Nat.succ (Nat.succ m)))
        (pow x (Nat.succ (Nat.succ m)))))
      (ratMul (ratMul (natRat (Nat.succ (Nat.succ m)))
        (pow B (Nat.succ m))) h) := by
  have diffEq :=
    pow_sub_pow_eq_mul_diffQuot x (ratAdd x h) (Nat.succ (Nat.succ m))
  have yMinusX : RatEq (ratSub (ratAdd x h) x) h :=
    ratSub_add_cancel_left x h
  have dq :=
    diffQuot_abs_bound_succ x (ratAdd x h) B hB hx hy (Nat.succ m)
  have mulBound :=
    ratAbs_mul_le
      (ratLe_of_RatEq_left
        (RatEq_trans _ _ _
          (BEDC.Derived.LocatedReal.ratAbs_respects yMinusX)
          (ratAbs_eq_self_of_nonneg_local hh))
        (ratLe_refl h))
      dq
  have leftBridge :
      RatEq
        (ratAbs (ratMul (ratSub (ratAdd x h) x)
          (diffQuot x (ratAdd x h) (Nat.succ (Nat.succ m)))))
        (ratAbs (ratSub (pow (ratAdd x h) (Nat.succ (Nat.succ m)))
          (pow x (Nat.succ (Nat.succ m))))) :=
    BEDC.Derived.LocatedReal.ratAbs_respects (RatEq_symm diffEq)
  have rightBridge :
      RatEq
        (ratMul h
          (ratMul (natRat (Nat.succ (Nat.succ m)))
            (pow B (Nat.succ m))))
        (ratMul (ratMul (natRat (Nat.succ (Nat.succ m)))
          (pow B (Nat.succ m))) h) :=
    ratMul_comm h
      (ratMul (natRat (Nat.succ (Nat.succ m))) (pow B (Nat.succ m)))
  exact ratLe_respects leftBridge rightBridge mulBound

private theorem avgErrNum_abs_bound_pos_step
    (x h B : BRat)
    (hh : ratLe ratZero h)
    (hB : ratLe ratZero B)
    (hx : ratLe (ratAbs x) B)
    (hy : ratLe (ratAbs (ratAdd x h)) B)
    (m : Nat)
    (ih : ratLe (ratAbs (avgErrNum x (ratAdd x h) (Nat.succ m)))
      (ratMul (ratMul (triRat (Nat.succ m)) (pow B m)) h)) :
    ratLe (ratAbs (avgErrNum x (ratAdd x h) (Nat.succ (Nat.succ m))))
      (ratMul (ratMul (triRat (Nat.succ (Nat.succ m))) (pow B (Nat.succ m))) h) := by
  have recStep := avgErrNum_succ x (ratAdd x h) (Nat.succ m)
  have diffBound :=
    avg_pow_diff_bound x h B hh hB hx hy m
  have prodBound :
      ratLe (ratAbs (ratMul x
        (avgErrNum x (ratAdd x h) (Nat.succ m))))
        (ratMul B (ratMul (ratMul (triRat (Nat.succ m)) (pow B m)) h)) :=
    ratAbs_mul_le hx ih
  have split :=
    BEDC.Derived.LocatedReal.ratAbs_triangle
      (ratSub (pow (ratAdd x h) (Nat.succ (Nat.succ m)))
        (pow x (Nat.succ (Nat.succ m))))
      (ratMul x (avgErrNum x (ratAdd x h) (Nat.succ m)))
  have addBound :=
    ratAdd_le_add diffBound prodBound
  exact ratLe_of_RatEq_right
    (ratLe_of_RatEq_left
      (BEDC.Derived.LocatedReal.ratAbs_respects recStep)
      (ratLe_trans split addBound))
    (avg_bound_step_alg B h m)

theorem avgErrNum_abs_bound_pos
    (x h B : BRat)
    (hh : ratLe ratZero h)
    (hB : ratLe ratZero B)
    (hx : ratLe (ratAbs x) B)
    (hy : ratLe (ratAbs (ratAdd x h)) B) :
    ∀ m : Nat,
      ratLe (ratAbs (avgErrNum x (ratAdd x h) (Nat.succ m)))
        (ratMul (ratMul (triRat (Nat.succ m)) (pow B m)) h)
  | 0 => avgErrNum_abs_bound_pos_zero x h B hh
  | Nat.succ m =>
      avgErrNum_abs_bound_pos_step x h B hh hB hx hy m
        (avgErrNum_abs_bound_pos x h B hh hB hx hy m)

private theorem ratDivNat_mul_cancel (x : BRat) (n : Nat) :
    RatEq (ratMul (ratDivNat x n) (natRat (Nat.succ n))) x := by
  unfold ratDivNat
  exact BEDC.Real.RatNumKernel.ratDivApart_mul_cancel_right
    (natRat_succ_apart n)

private theorem ratDivTwo_mul_cancel (x : BRat) :
    RatEq (ratMul (ratDivTwo x) ratTwoPanel) x := by
  unfold ratDivTwo ratTwoPanel
  exact BEDC.Real.RatNumKernel.ratDivApart_mul_cancel_right
    (natRat_succ_apart 1)

private theorem ratTwoPanel_pos :
    ratLt ratZero ratTwoPanel := by
  unfold ratTwoPanel
  exact natRat_succ_pos 1

private theorem ratTwoPanel_apart :
    ratApart0 ratTwoPanel := by
  unfold ratTwoPanel
  exact natRat_succ_apart 1

private theorem ratTwoPanel_nonneg :
    ratLe ratZero ratTwoPanel :=
  ratLt_to_ratLe ratTwoPanel_pos

private theorem ratNat_succ_right (n : Nat) :
    RatEq (ratAdd (natRat n) ratOne) (natRat (Nat.succ n)) :=
  RatEq_symm (ratNat_succ n)

private theorem ratTwoPanel_mul (x : BRat) :
    RatEq (ratMul ratTwoPanel x) (ratAdd x x) := by
  unfold ratTwoPanel
  change RatEq (ratMul (ratAdd ratOne ratOne) x) (ratAdd x x)
  exact RatEq_trans _ _ _
    (BEDC.Real.RatNumKernel.ratMul_add_right ratOne ratOne x)
    (ratAdd_respects (ratOne_mul_left x) (ratOne_mul_left x))

private theorem ratMul_twoPanel_right (x : BRat) :
    RatEq (ratMul x ratTwoPanel) (ratAdd x x) := by
  exact RatEq_trans _ _ _
    (ratMul_comm x ratTwoPanel)
    (ratTwoPanel_mul x)

private theorem ratAdd_self_eq_twoPanel_mul (x : BRat) :
    RatEq (ratAdd x x) (ratMul ratTwoPanel x) :=
  RatEq_symm (ratTwoPanel_mul x)

private theorem ratAdd_mul_two_copies (a b : BRat) :
    RatEq (ratAdd (ratMul a b) (ratAdd b b))
      (ratMul (ratAdd (ratAdd a ratOne) ratOne) b) := by
  have hCopies :
      RatEq (ratAdd b b)
        (ratMul (ratAdd ratOne ratOne) b) :=
    RatEq_trans
      (ratAdd b b)
      (ratAdd (ratMul ratOne b) (ratMul ratOne b))
      (ratMul (ratAdd ratOne ratOne) b)
      (ratAdd_respects
        (RatEq_symm (ratOne_mul_left b))
        (RatEq_symm (ratOne_mul_left b)))
      (RatEq_symm
        (BEDC.Real.RatNumKernel.ratMul_add_right ratOne ratOne b))
  have hCollect :
      RatEq
        (ratAdd (ratMul a b) (ratMul (ratAdd ratOne ratOne) b))
        (ratMul (ratAdd a (ratAdd ratOne ratOne)) b) :=
    RatEq_symm
      (BEDC.Real.RatNumKernel.ratMul_add_right
        a (ratAdd ratOne ratOne) b)
  have hAssoc :
      RatEq (ratAdd a (ratAdd ratOne ratOne))
        (ratAdd (ratAdd a ratOne) ratOne) :=
    RatEq_symm
      (BEDC.Derived.LocatedReal.ratAdd_assoc_local
        a ratOne ratOne)
  exact RatEq_trans
    (ratAdd (ratMul a b) (ratAdd b b))
    (ratAdd (ratMul a b) (ratMul (ratAdd ratOne ratOne) b))
    (ratMul (ratAdd (ratAdd a ratOne) ratOne) b)
    (ratAdd_respects (RatEq_refl (ratMul a b)) hCopies)
    (RatEq_trans
      (ratAdd (ratMul a b) (ratMul (ratAdd ratOne ratOne) b))
      (ratMul (ratAdd a (ratAdd ratOne ratOne)) b)
      (ratMul (ratAdd (ratAdd a ratOne) ratOne) b)
      hCollect
      (ratMul_respects hAssoc (RatEq_refl b)))

private theorem ratTwoPanel_as_natRat_two :
    RatEq ratTwoPanel (natRat 2) :=
  RatEq_refl ratTwoPanel

private theorem ratTwoPanel_as_ratNat_two :
    RatEq ratTwoPanel (ratNat 2) := by
  exact RatEq_trans
    ratTwoPanel
    (natRat 2)
    (ratNat 2)
    ratTwoPanel_as_natRat_two
    (natRat_as_ratNat 2)

private theorem two_mul_triRat_succ_step (m : Nat)
    (ih : RatEq (ratMul ratTwoPanel (triRat (Nat.succ m)))
      (ratMul (natRat (Nat.succ m)) (natRat (Nat.succ (Nat.succ m))))) :
    RatEq (ratMul ratTwoPanel (triRat (Nat.succ (Nat.succ m))))
      (ratMul (natRat (Nat.succ (Nat.succ m)))
        (natRat (Nat.succ (Nat.succ (Nat.succ m))))) := by
  let a : BRat := natRat (Nat.succ m)
  let b : BRat := natRat (Nat.succ (Nat.succ m))
  have bStep : RatEq b (ratAdd a ratOne) := by
    change RatEq (natRat (Nat.succ (Nat.succ m)))
      (ratAdd (natRat (Nat.succ m)) ratOne)
    exact ratNat_succ (Nat.succ m)
  have nextStep :
      RatEq (natRat (Nat.succ (Nat.succ (Nat.succ m))))
        (ratAdd b ratOne) := by
    change RatEq (natRat (Nat.succ (Nat.succ (Nat.succ m))))
      (ratAdd (natRat (Nat.succ (Nat.succ m))) ratOne)
    exact ratNat_succ (Nat.succ (Nat.succ m))
  have triStep :
      RatEq (triRat (Nat.succ (Nat.succ m)))
        (ratAdd (triRat (Nat.succ m)) b) := by
    change RatEq (ratAdd (triRat (Nat.succ m))
      (natRat (Nat.succ (Nat.succ m))))
      (ratAdd (triRat (Nat.succ m)) b)
    exact RatEq_refl _
  have expandLeft :
      RatEq (ratMul ratTwoPanel (triRat (Nat.succ (Nat.succ m))))
        (ratAdd (ratMul a b) (ratAdd b b)) := by
    exact RatEq_trans
      (ratMul ratTwoPanel (triRat (Nat.succ (Nat.succ m))))
      (ratMul ratTwoPanel (ratAdd (triRat (Nat.succ m)) b))
      (ratAdd (ratMul a b) (ratAdd b b))
      (ratMul_respects (RatEq_refl ratTwoPanel) triStep)
      (RatEq_trans
        (ratMul ratTwoPanel (ratAdd (triRat (Nat.succ m)) b))
        (ratAdd
          (ratMul ratTwoPanel (triRat (Nat.succ m)))
          (ratMul ratTwoPanel b))
        (ratAdd (ratMul a b) (ratAdd b b))
        (BEDC.Real.RatNumKernel.ratMul_add_left
          ratTwoPanel (triRat (Nat.succ m)) b)
        (ratAdd_respects ih (ratTwoPanel_mul b)))
  have factorLeft :
      RatEq (ratAdd (ratMul a b) (ratAdd b b))
        (ratMul (ratAdd (ratAdd a ratOne) ratOne) b) :=
    ratAdd_mul_two_copies a b
  have coeff :
      RatEq (ratAdd (ratAdd a ratOne) ratOne)
        (natRat (Nat.succ (Nat.succ (Nat.succ m)))) := by
    exact RatEq_trans
      (ratAdd (ratAdd a ratOne) ratOne)
      (ratAdd b ratOne)
      (natRat (Nat.succ (Nat.succ (Nat.succ m))))
      (ratAdd_respects (RatEq_symm bStep) (RatEq_refl ratOne))
      (RatEq_symm nextStep)
  have bTarget :
      RatEq b (natRat (Nat.succ (Nat.succ m))) := by
    exact RatEq_refl b
  have tailEq :
      RatEq (ratMul (ratAdd (ratAdd a ratOne) ratOne) b)
        (ratMul (natRat (Nat.succ (Nat.succ (Nat.succ m))))
          (natRat (Nat.succ (Nat.succ m)))) :=
    ratMul_respects coeff bTarget
  have targetComm :
      RatEq
        (ratMul (natRat (Nat.succ (Nat.succ (Nat.succ m))))
          (natRat (Nat.succ (Nat.succ m))))
        (ratMul (natRat (Nat.succ (Nat.succ m)))
          (natRat (Nat.succ (Nat.succ (Nat.succ m))))) :=
    ratMul_comm
      (natRat (Nat.succ (Nat.succ (Nat.succ m))))
      (natRat (Nat.succ (Nat.succ m)))
  have tailToTarget :
      RatEq (ratMul (ratAdd (ratAdd a ratOne) ratOne) b)
        (ratMul (natRat (Nat.succ (Nat.succ m)))
          (natRat (Nat.succ (Nat.succ (Nat.succ m))))) :=
    RatEq_trans
      (ratMul (ratAdd (ratAdd a ratOne) ratOne) b)
      (ratMul (natRat (Nat.succ (Nat.succ (Nat.succ m))))
        (natRat (Nat.succ (Nat.succ m))))
      (ratMul (natRat (Nat.succ (Nat.succ m)))
        (natRat (Nat.succ (Nat.succ (Nat.succ m)))))
      tailEq
      targetComm
  have midToTarget :
      RatEq (ratAdd (ratMul a b) (ratAdd b b))
        (ratMul (natRat (Nat.succ (Nat.succ m)))
          (natRat (Nat.succ (Nat.succ (Nat.succ m))))) :=
    RatEq_trans
      (ratAdd (ratMul a b) (ratAdd b b))
      (ratMul (ratAdd (ratAdd a ratOne) ratOne) b)
      (ratMul (natRat (Nat.succ (Nat.succ m)))
        (natRat (Nat.succ (Nat.succ (Nat.succ m)))))
      factorLeft
      tailToTarget
  exact RatEq_trans
    (ratMul ratTwoPanel (triRat (Nat.succ (Nat.succ m))))
    (ratAdd (ratMul a b) (ratAdd b b))
    (ratMul (natRat (Nat.succ (Nat.succ m)))
      (natRat (Nat.succ (Nat.succ (Nat.succ m)))))
    expandLeft
    midToTarget

theorem two_mul_triRat_succ (m : Nat) :
    RatEq (ratMul ratTwoPanel (triRat (Nat.succ m)))
      (ratMul (natRat (Nat.succ m)) (natRat (Nat.succ (Nat.succ m)))) := by
  induction m with
  | zero =>
      change RatEq (ratMul ratTwoPanel (ratAdd ratZero ratOne))
        (ratMul ratOne ratTwoPanel)
      exact RatEq_trans
        (ratMul ratTwoPanel (ratAdd ratZero ratOne))
        (ratMul ratTwoPanel ratOne)
        (ratMul ratOne ratTwoPanel)
        (ratMul_respects (RatEq_refl ratTwoPanel) (ratZero_add_left ratOne))
        (ratMul_comm ratTwoPanel ratOne)
  | succ m ih =>
      exact two_mul_triRat_succ_step m ih

theorem triRat_div_succ_succ (m : Nat) :
    RatEq (ratDivNat (triRat (Nat.succ m)) (Nat.succ m))
      (ratDivTwo (natRat (Nat.succ m))) := by
  let d : BRat := natRat (Nat.succ (Nat.succ m))
  let c : BRat := ratMul ratTwoPanel d
  have hc : ratApart0 c := by
    exact BEDC.Real.RatNumKernel.ratMul_apart0
      ratTwoPanel_apart (natRat_succ_apart (Nat.succ m))
  have leftAssoc :
      RatEq
        (ratMul (ratDivNat (triRat (Nat.succ m)) (Nat.succ m)) c)
        (ratMul
          (ratMul
            (ratDivNat (triRat (Nat.succ m)) (Nat.succ m))
            ratTwoPanel)
          d) := by
    change RatEq
      (ratMul (ratDivNat (triRat (Nat.succ m)) (Nat.succ m))
        (ratMul ratTwoPanel d))
      (ratMul
        (ratMul
          (ratDivNat (triRat (Nat.succ m)) (Nat.succ m))
          ratTwoPanel)
        d)
    exact RatEq_symm
      (ratMul_assoc
        (ratDivNat (triRat (Nat.succ m)) (Nat.succ m))
        ratTwoPanel d)
  have leftSwap :
      RatEq
        (ratMul
          (ratMul
            (ratDivNat (triRat (Nat.succ m)) (Nat.succ m))
            ratTwoPanel)
          d)
        (ratMul
          (ratMul ratTwoPanel
            (ratDivNat (triRat (Nat.succ m)) (Nat.succ m)))
          d) :=
    ratMul_respects
      (ratMul_comm
        (ratDivNat (triRat (Nat.succ m)) (Nat.succ m))
        ratTwoPanel)
      (RatEq_refl d)
  have leftRegroup :
      RatEq
        (ratMul
          (ratMul ratTwoPanel
            (ratDivNat (triRat (Nat.succ m)) (Nat.succ m)))
          d)
        (ratMul ratTwoPanel
          (ratMul
            (ratDivNat (triRat (Nat.succ m)) (Nat.succ m))
            d)) :=
    ratMul_assoc ratTwoPanel
      (ratDivNat (triRat (Nat.succ m)) (Nat.succ m)) d
  have leftDenCancel :
      RatEq
        (ratMul
          (ratDivNat (triRat (Nat.succ m)) (Nat.succ m))
          d)
        (triRat (Nat.succ m)) := by
    change RatEq
      (ratMul
        (ratDivNat (triRat (Nat.succ m)) (Nat.succ m))
        (natRat (Nat.succ (Nat.succ m))))
      (triRat (Nat.succ m))
    exact ratDivNat_mul_cancel (triRat (Nat.succ m)) (Nat.succ m)
  have leftCancel :
      RatEq
        (ratMul (ratDivNat (triRat (Nat.succ m)) (Nat.succ m)) c)
        (ratMul ratTwoPanel (triRat (Nat.succ m))) := by
    exact RatEq_trans
      (ratMul (ratDivNat (triRat (Nat.succ m)) (Nat.succ m)) c)
      (ratMul
        (ratMul
          (ratDivNat (triRat (Nat.succ m)) (Nat.succ m))
          ratTwoPanel)
        d)
      (ratMul ratTwoPanel (triRat (Nat.succ m)))
      leftAssoc
      (RatEq_trans
        (ratMul
          (ratMul
            (ratDivNat (triRat (Nat.succ m)) (Nat.succ m))
            ratTwoPanel)
          d)
        (ratMul
          (ratMul ratTwoPanel
            (ratDivNat (triRat (Nat.succ m)) (Nat.succ m)))
          d)
        (ratMul ratTwoPanel (triRat (Nat.succ m)))
        leftSwap
        (RatEq_trans
          (ratMul
            (ratMul ratTwoPanel
              (ratDivNat (triRat (Nat.succ m)) (Nat.succ m)))
            d)
          (ratMul ratTwoPanel
            (ratMul
              (ratDivNat (triRat (Nat.succ m)) (Nat.succ m))
              d))
          (ratMul ratTwoPanel (triRat (Nat.succ m)))
          leftRegroup
          (ratMul_respects (RatEq_refl ratTwoPanel) leftDenCancel)))
  have rightAssoc :
      RatEq
        (ratMul (ratDivTwo (natRat (Nat.succ m))) c)
        (ratMul
          (ratMul (ratDivTwo (natRat (Nat.succ m))) ratTwoPanel)
          d) := by
    change RatEq
      (ratMul (ratDivTwo (natRat (Nat.succ m)))
        (ratMul ratTwoPanel d))
      (ratMul
        (ratMul (ratDivTwo (natRat (Nat.succ m))) ratTwoPanel)
        d)
    exact RatEq_symm
      (ratMul_assoc (ratDivTwo (natRat (Nat.succ m))) ratTwoPanel d)
  have rightTwoCancel :
      RatEq (ratMul (ratDivTwo (natRat (Nat.succ m))) ratTwoPanel)
        (natRat (Nat.succ m)) :=
    ratDivTwo_mul_cancel (natRat (Nat.succ m))
  have rightCancel :
      RatEq
        (ratMul (ratDivTwo (natRat (Nat.succ m))) c)
        (ratMul (natRat (Nat.succ m)) d) := by
    exact RatEq_trans
      (ratMul (ratDivTwo (natRat (Nat.succ m))) c)
      (ratMul
        (ratMul (ratDivTwo (natRat (Nat.succ m))) ratTwoPanel)
        d)
      (ratMul (natRat (Nat.succ m)) d)
      rightAssoc
      (ratMul_respects
        rightTwoCancel
        (RatEq_refl d))
  have productEq :
      RatEq
        (ratMul (ratDivNat (triRat (Nat.succ m)) (Nat.succ m)) c)
        (ratMul (ratDivTwo (natRat (Nat.succ m))) c) :=
    RatEq_trans
      (ratMul (ratDivNat (triRat (Nat.succ m)) (Nat.succ m)) c)
      (ratMul ratTwoPanel (triRat (Nat.succ m)))
      (ratMul (ratDivTwo (natRat (Nat.succ m))) c)
      leftCancel
      (RatEq_trans
        (ratMul ratTwoPanel (triRat (Nat.succ m)))
        (ratMul (natRat (Nat.succ m)) d)
        (ratMul (ratDivTwo (natRat (Nat.succ m))) c)
        (two_mul_triRat_succ m)
        (RatEq_symm rightCancel))
  exact BEDC.Real.RatNumLogEnclosure.ratMul_right_cancel_apart0
    (ratDivNat (triRat (Nat.succ m)) (Nat.succ m))
    (ratDivTwo (natRat (Nat.succ m)))
    c hc productEq

private theorem ratMul_divNat_left_mul_cancel (h e : BRat) (k : Nat) :
    RatEq
      (ratMul (ratMul (ratDivNat h k) e) (natRat (Nat.succ k)))
      (ratMul h e) := by
  let n : BRat := natRat (Nat.succ k)
  have stepAssoc :
      RatEq (ratMul (ratMul (ratDivNat h k) e) n)
        (ratMul (ratDivNat h k) (ratMul e n)) :=
    ratMul_assoc (ratDivNat h k) e n
  have stepSwap :
      RatEq (ratMul (ratDivNat h k) (ratMul e n))
        (ratMul (ratDivNat h k) (ratMul n e)) :=
    ratMul_respects (RatEq_refl (ratDivNat h k)) (ratMul_comm e n)
  have stepRegroup :
      RatEq (ratMul (ratDivNat h k) (ratMul n e))
        (ratMul (ratMul (ratDivNat h k) n) e) :=
    RatEq_symm (ratMul_assoc (ratDivNat h k) n e)
  have stepCancel :
      RatEq (ratMul (ratMul (ratDivNat h k) n) e) (ratMul h e) :=
    ratMul_respects (ratDivNat_mul_cancel h k) (RatEq_refl e)
  exact RatEq_trans
    (ratMul (ratMul (ratDivNat h k) e) (natRat (Nat.succ k)))
    (ratMul (ratDivNat h k) (ratMul e n))
    (ratMul h e)
    stepAssoc
    (RatEq_trans
      (ratMul (ratDivNat h k) (ratMul e n))
      (ratMul (ratDivNat h k) (ratMul n e))
      (ratMul h e)
      stepSwap
      (RatEq_trans
        (ratMul (ratDivNat h k) (ratMul n e))
        (ratMul (ratMul (ratDivNat h k) n) e)
        (ratMul h e)
        stepRegroup
        stepCancel))

private theorem ratSub_divNat_mul_den
    (a b : BRat) (k : Nat) :
    RatEq
      (ratMul (ratSub (ratDivNat a k) b) (natRat (Nat.succ k)))
      (ratSub a (ratMul b (natRat (Nat.succ k)))) := by
  have dist :
      RatEq
        (ratMul (ratSub (ratDivNat a k) b) (natRat (Nat.succ k)))
        (ratSub
          (ratMul (ratDivNat a k) (natRat (Nat.succ k)))
          (ratMul b (natRat (Nat.succ k)))) :=
    ratSub_mul_right (ratDivNat a k) b (natRat (Nat.succ k))
  have cancel :
      RatEq
        (ratSub
          (ratMul (ratDivNat a k) (natRat (Nat.succ k)))
          (ratMul b (natRat (Nat.succ k))))
        (ratSub a (ratMul b (natRat (Nat.succ k)))) :=
    ratSub_respects (ratDivNat_mul_cancel a k)
      (RatEq_refl (ratMul b (natRat (Nat.succ k))))
  exact RatEq_trans
    (ratMul (ratSub (ratDivNat a k) b) (natRat (Nat.succ k)))
    (ratSub
      (ratMul (ratDivNat a k) (natRat (Nat.succ k)))
      (ratMul b (natRat (Nat.succ k))))
    (ratSub a (ratMul b (natRat (Nat.succ k))))
    dist
    cancel

theorem monoPanelErr_eq (x h : BRat) (k : Nat) :
    RatEq (monoPanelErr x h k)
      (ratMul (ratDivNat h k) (avgErrNum x (ratAdd x h) k)) := by
  let n : BRat := natRat (Nat.succ k)
  let p : BRat := pow x k
  let dq : BRat := diffQuot x (ratAdd x h) (Nat.succ k)
  let d : BRat :=
    ratSub (pow (ratAdd x h) (Nat.succ k)) (pow x (Nat.succ k))
  have denomApart : ratApart0 n := by
    unfold n
    exact natRat_succ_apart k
  apply BEDC.Real.RatNumLogEnclosure.ratMul_right_cancel_apart0
    (monoPanelErr x h k)
    (ratMul (ratDivNat h k) (avgErrNum x (ratAdd x h) k))
    n denomApart
  have leftProd :
      RatEq (ratMul (monoPanelErr x h k) n)
        (ratSub d (ratMul (ratMul h p) n)) := by
    unfold monoPanelErr d p n
    exact ratSub_divNat_mul_den
      (ratSub (pow (ratAdd x h) (Nat.succ k)) (pow x (Nat.succ k)))
      (ratMul h (pow x k)) k
  have yMinusX : RatEq (ratSub (ratAdd x h) x) h :=
    ratSub_add_cancel_left x h
  have diffRaw :
      RatEq d (ratMul (ratSub (ratAdd x h) x) dq) := by
    unfold d dq
    exact pow_sub_pow_eq_mul_diffQuot x (ratAdd x h) (Nat.succ k)
  have diffAsH :
      RatEq d (ratMul h dq) := by
    exact RatEq_trans
      d
      (ratMul (ratSub (ratAdd x h) x) dq)
      (ratMul h dq)
      diffRaw
      (ratMul_respects yMinusX (RatEq_refl dq))
  have secondTerm :
      RatEq (ratMul (ratMul h p) n) (ratMul h (ratMul n p)) := by
    unfold n p
    exact ratMul_assoc_swap_last h (pow x k) (natRat (Nat.succ k))
  have leftToExpanded :
      RatEq (ratSub d (ratMul (ratMul h p) n))
        (ratSub (ratMul h dq) (ratMul h (ratMul n p))) :=
    ratSub_respects diffAsH secondTerm
  have avgExpand :
      RatEq (ratMul h (avgErrNum x (ratAdd x h) k))
        (ratSub (ratMul h dq) (ratMul h (ratMul n p))) := by
    unfold avgErrNum dq n p
    exact ratSub_mul_left h
      (diffQuot x (ratAdd x h) (Nat.succ k))
      (ratMul (natRat (Nat.succ k)) (pow x k))
  have rightProd :
      RatEq
        (ratMul
          (ratMul (ratDivNat h k) (avgErrNum x (ratAdd x h) k))
          n)
        (ratMul h (avgErrNum x (ratAdd x h) k)) := by
    unfold n
    exact ratMul_divNat_left_mul_cancel h
      (avgErrNum x (ratAdd x h) k) k
  exact RatEq_trans
    (ratMul (monoPanelErr x h k) n)
    (ratSub d (ratMul (ratMul h p) n))
    (ratMul
      (ratMul (ratDivNat h k) (avgErrNum x (ratAdd x h) k))
      n)
    leftProd
    (RatEq_trans
      (ratSub d (ratMul (ratMul h p) n))
      (ratSub (ratMul h dq) (ratMul h (ratMul n p)))
      (ratMul
        (ratMul (ratDivNat h k) (avgErrNum x (ratAdd x h) k))
        n)
      leftToExpanded
      (RatEq_trans
        (ratSub (ratMul h dq) (ratMul h (ratMul n p)))
        (ratMul h (avgErrNum x (ratAdd x h) k))
        (ratMul
          (ratMul (ratDivNat h k) (avgErrNum x (ratAdd x h) k))
          n)
        (RatEq_symm avgExpand)
        (RatEq_symm rightProd)))

private theorem ratDivTwo_nonneg {x : BRat}
    (hx : ratLe ratZero x) :
    ratLe ratZero (ratDivTwo x) := by
  unfold ratDivTwo ratTwoPanel
  exact BEDC.Real.RatNumKernel.ratDivApart_nonneg_of_nonneg_pos
    hx (natRat_succ_pos 1) (natRat_succ_apart 1)

private theorem ratDivNat_nonneg {x : BRat} (k : Nat)
    (hx : ratLe ratZero x) :
    ratLe ratZero (ratDivNat x k) := by
  unfold ratDivNat
  exact BEDC.Real.RatNumKernel.ratDivApart_nonneg_of_nonneg_pos
    hx (natRat_succ_pos k) (natRat_succ_apart k)

private theorem ratDivNat_abs_of_nonneg {x : BRat} (k : Nat)
    (hx : ratLe ratZero x) :
    RatEq (ratAbs (ratDivNat x k)) (ratDivNat x k) :=
  ratAbs_eq_self_of_nonneg_local (ratDivNat_nonneg k hx)

private theorem pow_nonneg (z : BRat)
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
      change ratLe ratZero
        (ratMul (natRat (Nat.succ m)) (pow B m))
      exact ratMul_nonneg
        (ratLt_to_ratLe (natRat_succ_pos m))
        (pow_nonneg B hB m)

private theorem ratDivNat_mul_comm (a b : BRat) (k : Nat) :
    RatEq (ratMul (ratDivNat a k) b) (ratMul (ratDivNat b k) a) := by
  let n : BRat := natRat (Nat.succ k)
  have hn : ratApart0 n := by
    unfold n
    exact natRat_succ_apart k
  apply BEDC.Real.RatNumLogEnclosure.ratMul_right_cancel_apart0
    (ratMul (ratDivNat a k) b)
    (ratMul (ratDivNat b k) a)
    n hn
  have leftAssoc :
      RatEq (ratMul (ratMul (ratDivNat a k) b) n)
        (ratMul (ratDivNat a k) (ratMul b n)) :=
    ratMul_assoc (ratDivNat a k) b n
  have leftSwap :
      RatEq (ratMul (ratDivNat a k) (ratMul b n))
        (ratMul (ratDivNat a k) (ratMul n b)) :=
    ratMul_respects (RatEq_refl (ratDivNat a k)) (ratMul_comm b n)
  have leftRegroup :
      RatEq (ratMul (ratDivNat a k) (ratMul n b))
        (ratMul (ratMul (ratDivNat a k) n) b) :=
    RatEq_symm (ratMul_assoc (ratDivNat a k) n b)
  have leftCancel :
      RatEq (ratMul (ratMul (ratDivNat a k) n) b)
        (ratMul a b) :=
    ratMul_respects (ratDivNat_mul_cancel a k) (RatEq_refl b)
  have leftToAB :
      RatEq (ratMul (ratMul (ratDivNat a k) b) n)
        (ratMul a b) :=
    RatEq_trans
      (ratMul (ratMul (ratDivNat a k) b) n)
      (ratMul (ratDivNat a k) (ratMul b n))
      (ratMul a b)
      leftAssoc
      (RatEq_trans
        (ratMul (ratDivNat a k) (ratMul b n))
        (ratMul (ratDivNat a k) (ratMul n b))
        (ratMul a b)
        leftSwap
        (RatEq_trans
          (ratMul (ratDivNat a k) (ratMul n b))
          (ratMul (ratMul (ratDivNat a k) n) b)
          (ratMul a b)
          leftRegroup
          leftCancel))
  have rightAssoc :
      RatEq (ratMul (ratMul (ratDivNat b k) a) n)
        (ratMul (ratDivNat b k) (ratMul a n)) :=
    ratMul_assoc (ratDivNat b k) a n
  have rightSwap :
      RatEq (ratMul (ratDivNat b k) (ratMul a n))
        (ratMul (ratDivNat b k) (ratMul n a)) :=
    ratMul_respects (RatEq_refl (ratDivNat b k)) (ratMul_comm a n)
  have rightRegroup :
      RatEq (ratMul (ratDivNat b k) (ratMul n a))
        (ratMul (ratMul (ratDivNat b k) n) a) :=
    RatEq_symm (ratMul_assoc (ratDivNat b k) n a)
  have rightCancel :
      RatEq (ratMul (ratMul (ratDivNat b k) n) a)
        (ratMul b a) :=
    ratMul_respects (ratDivNat_mul_cancel b k) (RatEq_refl a)
  have rightToBA :
      RatEq (ratMul (ratMul (ratDivNat b k) a) n)
        (ratMul b a) :=
    RatEq_trans
      (ratMul (ratMul (ratDivNat b k) a) n)
      (ratMul (ratDivNat b k) (ratMul a n))
      (ratMul b a)
      rightAssoc
      (RatEq_trans
        (ratMul (ratDivNat b k) (ratMul a n))
        (ratMul (ratDivNat b k) (ratMul n a))
        (ratMul b a)
        rightSwap
        (RatEq_trans
          (ratMul (ratDivNat b k) (ratMul n a))
          (ratMul (ratMul (ratDivNat b k) n) a)
          (ratMul b a)
          rightRegroup
          rightCancel))
  exact RatEq_trans
    (ratMul (ratMul (ratDivNat a k) b) n)
    (ratMul a b)
    (ratMul (ratMul (ratDivNat b k) a) n)
    leftToAB
    (RatEq_trans
      (ratMul a b)
      (ratMul b a)
      (ratMul (ratMul (ratDivNat b k) a) n)
      (ratMul_comm a b)
      (RatEq_symm rightToBA))

private theorem ratMul_repack_square (q p h : BRat) :
    RatEq (ratMul (ratMul (ratMul q h) p) h)
      (ratMul (ratMul q p) (ratMul h h)) := by
  have step1 :
      RatEq (ratMul (ratMul (ratMul q h) p) h)
        (ratMul (ratMul q h) (ratMul p h)) :=
    ratMul_assoc (ratMul q h) p h
  have step2 :
      RatEq (ratMul (ratMul q h) (ratMul p h))
        (ratMul (ratMul q h) (ratMul h p)) :=
    ratMul_respects (RatEq_refl (ratMul q h)) (ratMul_comm p h)
  have step3 :
      RatEq (ratMul (ratMul q h) (ratMul h p))
        (ratMul q (ratMul h (ratMul h p))) :=
    ratMul_assoc q h (ratMul h p)
  have step4 :
      RatEq (ratMul q (ratMul h (ratMul h p)))
        (ratMul q (ratMul (ratMul h h) p)) :=
    ratMul_respects (RatEq_refl q)
      (RatEq_symm (ratMul_assoc h h p))
  have step5 :
      RatEq (ratMul q (ratMul (ratMul h h) p))
        (ratMul q (ratMul p (ratMul h h))) :=
    ratMul_respects (RatEq_refl q) (ratMul_comm (ratMul h h) p)
  have step6 :
      RatEq (ratMul q (ratMul p (ratMul h h)))
        (ratMul (ratMul q p) (ratMul h h)) :=
    RatEq_symm (ratMul_assoc q p (ratMul h h))
  exact RatEq_trans
    (ratMul (ratMul (ratMul q h) p) h)
    (ratMul (ratMul q h) (ratMul p h))
    (ratMul (ratMul q p) (ratMul h h))
    step1
    (RatEq_trans
      (ratMul (ratMul q h) (ratMul p h))
      (ratMul (ratMul q h) (ratMul h p))
      (ratMul (ratMul q p) (ratMul h h))
      step2
      (RatEq_trans
        (ratMul (ratMul q h) (ratMul h p))
        (ratMul q (ratMul h (ratMul h p)))
        (ratMul (ratMul q p) (ratMul h h))
        step3
        (RatEq_trans
          (ratMul q (ratMul h (ratMul h p)))
          (ratMul q (ratMul (ratMul h h) p))
          (ratMul (ratMul q p) (ratMul h h))
          step4
          (RatEq_trans
            (ratMul q (ratMul (ratMul h h) p))
            (ratMul q (ratMul p (ratMul h h)))
            (ratMul (ratMul q p) (ratMul h h))
            step5
            step6))))

private theorem ratMul_divTwo_left_mul_cancel (a e : BRat) :
    RatEq (ratMul (ratMul (ratDivTwo a) e) ratTwoPanel)
      (ratMul a e) := by
  have stepAssoc :
      RatEq (ratMul (ratMul (ratDivTwo a) e) ratTwoPanel)
        (ratMul (ratDivTwo a) (ratMul e ratTwoPanel)) :=
    ratMul_assoc (ratDivTwo a) e ratTwoPanel
  have stepSwap :
      RatEq (ratMul (ratDivTwo a) (ratMul e ratTwoPanel))
        (ratMul (ratDivTwo a) (ratMul ratTwoPanel e)) :=
    ratMul_respects (RatEq_refl (ratDivTwo a))
      (ratMul_comm e ratTwoPanel)
  have stepRegroup :
      RatEq (ratMul (ratDivTwo a) (ratMul ratTwoPanel e))
        (ratMul (ratMul (ratDivTwo a) ratTwoPanel) e) :=
    RatEq_symm (ratMul_assoc (ratDivTwo a) ratTwoPanel e)
  have stepCancel :
      RatEq (ratMul (ratMul (ratDivTwo a) ratTwoPanel) e)
        (ratMul a e) :=
    ratMul_respects (ratDivTwo_mul_cancel a) (RatEq_refl e)
  exact RatEq_trans
    (ratMul (ratMul (ratDivTwo a) e) ratTwoPanel)
    (ratMul (ratDivTwo a) (ratMul e ratTwoPanel))
    (ratMul a e)
    stepAssoc
    (RatEq_trans
      (ratMul (ratDivTwo a) (ratMul e ratTwoPanel))
      (ratMul (ratDivTwo a) (ratMul ratTwoPanel e))
      (ratMul a e)
      stepSwap
      (RatEq_trans
        (ratMul (ratDivTwo a) (ratMul ratTwoPanel e))
        (ratMul (ratMul (ratDivTwo a) ratTwoPanel) e)
        (ratMul a e)
        stepRegroup
        stepCancel))

private theorem ratDivTwo_mul_left (a b : BRat) :
    RatEq (ratMul (ratDivTwo a) b) (ratDivTwo (ratMul a b)) := by
  apply BEDC.Real.RatNumLogEnclosure.ratMul_right_cancel_apart0
    (ratMul (ratDivTwo a) b)
    (ratDivTwo (ratMul a b))
    ratTwoPanel ratTwoPanel_apart
  exact RatEq_trans
    (ratMul (ratMul (ratDivTwo a) b) ratTwoPanel)
    (ratMul a b)
    (ratMul (ratDivTwo (ratMul a b)) ratTwoPanel)
    (ratMul_divTwo_left_mul_cancel a b)
    (RatEq_symm (ratDivTwo_mul_cancel (ratMul a b)))

private theorem monoPanelErr_zero_eq (x h : BRat) :
    RatEq (monoPanelErr x h 0) ratZero := by
  have eqMono := monoPanelErr_eq x h 0
  have avgZero : RatEq (avgErrNum x (ratAdd x h) 0) ratZero :=
    avgErr_zero x (ratAdd x h)
  exact RatEq_trans
    (monoPanelErr x h 0)
    (ratMul (ratDivNat h 0) (avgErrNum x (ratAdd x h) 0))
    ratZero
    eqMono
    (RatEq_trans
      (ratMul (ratDivNat h 0) (avgErrNum x (ratAdd x h) 0))
      (ratMul (ratDivNat h 0) ratZero)
      ratZero
      (ratMul_respects (RatEq_refl (ratDivNat h 0)) avgZero)
      (ratMul_zero_right_local (ratDivNat h 0)))

private theorem zero_panel_rhs_eq (h B : BRat) :
    RatEq
      (ratDivTwo (ratMul (degWeight 0 B) (ratMul h h)))
      ratZero := by
  change RatEq (ratDivTwo (ratMul ratZero (ratMul h h))) ratZero
  have innerZero :
      RatEq (ratMul ratZero (ratMul h h)) ratZero :=
    ratMul_zero_left_local (ratMul h h)
  apply BEDC.Real.RatNumLogEnclosure.ratMul_right_cancel_apart0
    (ratDivTwo (ratMul ratZero (ratMul h h)))
    ratZero
    ratTwoPanel ratTwoPanel_apart
  have left :
      RatEq
        (ratMul (ratDivTwo (ratMul ratZero (ratMul h h))) ratTwoPanel)
        (ratMul ratZero ratTwoPanel) :=
    RatEq_trans
      (ratMul (ratDivTwo (ratMul ratZero (ratMul h h))) ratTwoPanel)
      (ratMul ratZero (ratMul h h))
      (ratMul ratZero ratTwoPanel)
      (ratDivTwo_mul_cancel (ratMul ratZero (ratMul h h)))
      (RatEq_trans
        (ratMul ratZero (ratMul h h))
        ratZero
        (ratMul ratZero ratTwoPanel)
        innerZero
        (RatEq_symm (ratMul_zero_left_local ratTwoPanel)))
  exact left

theorem monomial_panel_error
    (x h B : BRat)
    (hh : ratLe ratZero h)
    (hB : ratLe ratZero B)
    (hx : ratLe (ratAbs x) B)
    (hy : ratLe (ratAbs (ratAdd x h)) B) :
    ∀ k : Nat,
      ratLe (ratAbs (monoPanelErr x h k))
        (ratDivTwo (ratMul (degWeight k B) (ratMul h h)))
  | 0 => by
      have leftZero :
          RatEq (ratAbs (monoPanelErr x h 0)) ratZero := by
        exact RatEq_trans
          (ratAbs (monoPanelErr x h 0))
          (ratAbs ratZero)
          ratZero
          (BEDC.Derived.LocatedReal.ratAbs_respects
            (monoPanelErr_zero_eq x h))
          (ratAbs_eq_self_of_nonneg_local (ratLe_refl ratZero))
      exact ratLe_respects
        (RatEq_symm leftZero)
        (RatEq_symm (zero_panel_rhs_eq h B))
        (ratLe_refl ratZero)
  | Nat.succ m => by
      have avgBound :=
        avgErrNum_abs_bound_pos x h B hh hB hx hy m
      have monoEq := monoPanelErr_eq x h (Nat.succ m)
      have hAbsDiv :
          RatEq (ratAbs (ratDivNat h (Nat.succ m)))
            (ratDivNat h (Nat.succ m)) :=
        ratDivNat_abs_of_nonneg (Nat.succ m) hh
      have first :
          ratLe
            (ratAbs
              (ratMul (ratDivNat h (Nat.succ m))
                (avgErrNum x (ratAdd x h) (Nat.succ m))))
            (ratMul (ratDivNat h (Nat.succ m))
              (ratMul (ratMul (triRat (Nat.succ m)) (pow B m)) h)) := by
        have divBound :
            ratLe (ratAbs (ratDivNat h (Nat.succ m)))
              (ratDivNat h (Nat.succ m)) :=
          BEDC.Real.RatNumKernel.ratLe_of_RatEq_left
            hAbsDiv
            (ratLe_refl (ratDivNat h (Nat.succ m)))
        exact ratAbs_mul_le divBound avgBound
      -- The remaining normalization is the monomial coefficient identity.
      have rhsBridge :
          RatEq
            (ratMul (ratDivNat h (Nat.succ m))
              (ratMul (ratMul (triRat (Nat.succ m)) (pow B m)) h))
            (ratDivTwo
              (ratMul (degWeight (Nat.succ m) B) (ratMul h h))) := by
        let p : BRat := pow B m
        let t : BRat := triRat (Nat.succ m)
        let q : BRat := natRat (Nat.succ m)
        have divSwap :
            RatEq (ratMul (ratDivNat h (Nat.succ m)) t)
              (ratMul (ratDivNat t (Nat.succ m)) h) :=
          ratDivNat_mul_comm h t (Nat.succ m)
        have divTri :
            RatEq (ratDivNat t (Nat.succ m)) (ratDivTwo q) := by
          unfold t q
          exact triRat_div_succ_succ m
        have firstPack :
            RatEq
              (ratMul (ratDivNat h (Nat.succ m))
                (ratMul (ratMul t p) h))
              (ratMul (ratMul (ratMul (ratDivTwo q) h) p) h) := by
          have assoc1 :
              RatEq
                (ratMul (ratDivNat h (Nat.succ m))
                  (ratMul (ratMul t p) h))
                (ratMul (ratMul (ratDivNat h (Nat.succ m))
                  (ratMul t p)) h) :=
            RatEq_symm
              (ratMul_assoc (ratDivNat h (Nat.succ m))
                (ratMul t p) h)
          have assoc2 :
              RatEq
                (ratMul (ratMul (ratDivNat h (Nat.succ m))
                  (ratMul t p)) h)
                (ratMul (ratMul
                  (ratMul (ratDivNat h (Nat.succ m)) t) p) h) :=
            ratMul_respects
              (RatEq_symm
                (ratMul_assoc (ratDivNat h (Nat.succ m)) t p))
              (RatEq_refl h)
          have replaceDiv :
              RatEq
                (ratMul (ratMul
                  (ratMul (ratDivNat h (Nat.succ m)) t) p) h)
                (ratMul (ratMul (ratMul (ratDivTwo q) h) p) h) :=
            ratMul_respects
              (ratMul_respects
                (RatEq_trans
                  (ratMul (ratDivNat h (Nat.succ m)) t)
                  (ratMul (ratDivNat t (Nat.succ m)) h)
                  (ratMul (ratDivTwo q) h)
                  divSwap
                  (ratMul_respects divTri (RatEq_refl h)))
                (RatEq_refl p))
              (RatEq_refl h)
          exact RatEq_trans
            (ratMul (ratDivNat h (Nat.succ m))
              (ratMul (ratMul t p) h))
            (ratMul (ratMul (ratDivNat h (Nat.succ m))
              (ratMul t p)) h)
            (ratMul (ratMul (ratMul (ratDivTwo q) h) p) h)
            assoc1
            (RatEq_trans
              (ratMul (ratMul (ratDivNat h (Nat.succ m))
                (ratMul t p)) h)
              (ratMul (ratMul
                (ratMul (ratDivNat h (Nat.succ m)) t) p) h)
              (ratMul (ratMul (ratMul (ratDivTwo q) h) p) h)
              assoc2
              replaceDiv)
        have repack :
            RatEq (ratMul (ratMul (ratMul (ratDivTwo q) h) p) h)
              (ratMul (ratMul (ratDivTwo q) p) (ratMul h h)) :=
          ratMul_repack_square (ratDivTwo q) p h
        have pullHalf :
            RatEq (ratMul (ratMul (ratDivTwo q) p) (ratMul h h))
              (ratDivTwo (ratMul (ratMul q p) (ratMul h h))) := by
          have halfCoeff :
              RatEq (ratMul (ratDivTwo q) p)
                (ratDivTwo (ratMul q p)) :=
            ratDivTwo_mul_left q p
          exact RatEq_trans
            (ratMul (ratMul (ratDivTwo q) p) (ratMul h h))
            (ratMul (ratDivTwo (ratMul q p)) (ratMul h h))
            (ratDivTwo (ratMul (ratMul q p) (ratMul h h)))
            (ratMul_respects halfCoeff (RatEq_refl (ratMul h h)))
            (ratDivTwo_mul_left (ratMul q p) (ratMul h h))
        have target :
            RatEq (ratDivTwo (ratMul (ratMul q p) (ratMul h h)))
              (ratDivTwo
                (ratMul (degWeight (Nat.succ m) B) (ratMul h h))) := by
          unfold q p
          change RatEq
            (ratDivTwo
              (ratMul
                (ratMul (natRat (Nat.succ m)) (pow B m))
                (ratMul h h)))
            (ratDivTwo
              (ratMul
                (ratMul (natRat (Nat.succ m)) (pow B m))
                (ratMul h h)))
          exact RatEq_refl _
        exact RatEq_trans
          (ratMul (ratDivNat h (Nat.succ m))
            (ratMul (ratMul (triRat (Nat.succ m)) (pow B m)) h))
          (ratMul (ratMul (ratMul (ratDivTwo q) h) p) h)
          (ratDivTwo
            (ratMul (degWeight (Nat.succ m) B) (ratMul h h)))
          firstPack
          (RatEq_trans
            (ratMul (ratMul (ratMul (ratDivTwo q) h) p) h)
            (ratMul (ratMul (ratDivTwo q) p) (ratMul h h))
            (ratDivTwo
              (ratMul (degWeight (Nat.succ m) B) (ratMul h h)))
            repack
            (RatEq_trans
              (ratMul (ratMul (ratDivTwo q) p) (ratMul h h))
              (ratDivTwo (ratMul (ratMul q p) (ratMul h h)))
              (ratDivTwo
                (ratMul (degWeight (Nat.succ m) B) (ratMul h h)))
              pullHalf
              target))
      exact ratLe_of_RatEq_right
        (ratLe_of_RatEq_left
          (BEDC.Derived.LocatedReal.ratAbs_respects monoEq)
          first)
        rhsBridge

end BEDC.Derived.RHRoute.IntervalMatrixPSD
