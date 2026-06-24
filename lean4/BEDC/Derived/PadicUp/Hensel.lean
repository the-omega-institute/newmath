import BEDC.Derived.PadicUp.FieldCore

namespace BEDC.Derived.PadicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.PrimeUp
open BEDC.Derived.IntUp

def ZpPoly (p : BHist) : Type :=
  List (ZpInt p)

def zpNatCoeff {p : BHist} (prime : NatPrime p) (n : Nat) : ZpInt p :=
  zpOfNat p prime (zpuNatToUnary n) (zpuNatToUnary_unary n)

def zpEval {p : BHist} : ZpPoly p -> ZpInt p -> ZpInt p
  | [], x => zpZero p x.prime
  | [c], _x => c
  | c :: d :: cs, x => zpAdd p c (zpMul p x (zpEval (d :: cs) x))

def zpDerivAux {p : BHist} (prime : NatPrime p) : Nat -> ZpPoly p -> ZpPoly p
  | _i, [] => []
  | i, _c :: cs =>
      match cs with
      | [] => []
      | d :: ds => zpMul p (zpNatCoeff prime (i + 1)) d :: zpDerivAux prime (i + 1) (d :: ds)

def zpDeriv {p : BHist} (f : ZpPoly p) : ZpPoly p :=
  match f with
  | [] => []
  | c :: cs => zpDerivAux c.prime 0 (c :: cs)

def zpLinearPoly {p : BHist} (b m : ZpInt p) : ZpPoly p :=
  [b, m]

structure HenselData {p : BHist} (f : ZpPoly p) where
  a0 : ZpInt p
  root_mod_p :
    (zpLevel (zpEval f a0) (zpuNatToUnary 1) (zpuNatToUnary_unary 1)).val =
      BHist.Empty
  deriv_unit : ZpUnit (zpEval (zpDeriv f) a0)

def newtonStep {p : BHist} (f : ZpPoly p) (a : ZpInt p)
    (unit : ZpUnit (zpEval (zpDeriv f) a)) : ZpInt p :=
  zpSub p a (zpMul p (zpEval f a) (ZpUnitInv (zpEval (zpDeriv f) a) unit))

theorem ZpUnit_of_ZpEq {p : BHist} {x y : ZpInt p} :
    ZpEq x y -> ZpUnit y -> ZpUnit x := by
  intro same unit sameZero
  exact unit (hsame_trans (hsame_symm (same (BHist.e1 BHist.Empty)
    (unary_e1_closed unary_empty))) sameZero)

theorem zpEval_linear {p : BHist} (b m x : ZpInt p) :
    ZpEq (zpEval (zpLinearPoly b m) x) (zpAdd p b (zpMul p x m)) := by
  exact ZpEq_refl _

theorem zpDeriv_linear {p : BHist} (b m : ZpInt p) :
    zpDeriv (zpLinearPoly b m) = [zpMul p (zpNatCoeff b.prime 1) m] := by
  rfl

theorem zpNatCoeff_one_mul {p : BHist} (prime : NatPrime p) (x : ZpInt p) :
    ZpEq (zpMul p (zpNatCoeff prime 1) x) x := by
  unfold zpNatCoeff
  exact zpOne_mul_left p prime x

theorem zpEval_deriv_linear {p : BHist} (b m x : ZpInt p) :
    ZpEq (zpEval (zpDeriv (zpLinearPoly b m)) x) m := by
  change ZpEq (zpMul p (zpNatCoeff b.prime 1) m) m
  exact zpNatCoeff_one_mul b.prime m

def linearHenselUnit {p : BHist} (b m a0 : ZpInt p) (unit : ZpUnit m) :
    ZpUnit (zpEval (zpDeriv (zpLinearPoly b m)) a0) :=
  ZpUnit_of_ZpEq (zpEval_deriv_linear b m a0) unit

def linearHenselRoot {p : BHist} (b m a0 : ZpInt p) (unit : ZpUnit m) :
    ZpInt p :=
  newtonStep (zpLinearPoly b m) a0 (linearHenselUnit b m a0 unit)

theorem zpSub_self_eq_zero {p : BHist} (x : ZpInt p) :
    ZpEq (zpSub p x x) (zpZero p x.prime) := by
  unfold zpSub
  exact zpAdd_neg_right p x

theorem zpNeg_congr {p : BHist} {x y : ZpInt p} :
    ZpEq x y -> ZpEq (zpNeg p x) (zpNeg p y) := by
  intro same
  intro N NUnary
  unfold zpNeg zpNegTrunc fromNatModPow natMod
  exact natModFn_hsame_arg_transport (M := pPowCanon p N)
    (natComplementMod_hsame_arg_transport (same N NUnary))

theorem zpSub_congr {p : BHist} {x x' y y' : ZpInt p} :
    ZpEq x x' -> ZpEq y y' -> ZpEq (zpSub p x y) (zpSub p x' y') := by
  intro sameX sameY
  unfold zpSub
  exact zpAdd_congr sameX (zpNeg_congr sameY)

theorem linearHenselRoot_mul_slope {p : BHist}
    (b m a0 : ZpInt p) (unit : ZpUnit m) :
    ZpEq (zpMul p (linearHenselRoot b m a0 unit) m)
      (zpSub p (zpMul p a0 m) (zpAdd p b (zpMul p a0 m))) := by
  let d := zpEval (zpDeriv (zpLinearPoly b m)) a0
  let dinv := ZpUnitInv d (linearHenselUnit b m a0 unit)
  let fa := zpAdd p b (zpMul p a0 m)
  have rootUnfold :
      ZpEq (linearHenselRoot b m a0 unit)
        (zpSub p a0 (zpMul p fa dinv)) := by
    unfold linearHenselRoot newtonStep
    exact zpSub_congr (ZpEq_refl a0)
      (zpMul_left_congr (zpEval_linear b m a0))
  have mulRoot :
      ZpEq (zpMul p (linearHenselRoot b m a0 unit) m)
        (zpMul p (zpSub p a0 (zpMul p fa dinv)) m) :=
    zpMul_left_congr rootUnfold
  have subTail :
      ZpEq (zpMul p (zpSub p a0 (zpMul p fa dinv)) m)
        (zpSub p (zpMul p a0 m) (zpMul p (zpMul p fa dinv) m)) := by
    apply zpAdd_cancel_right (z := zpMul p (zpMul p fa dinv) m)
    have tailComm :
        ZpEq (zpMul p (zpMul p fa dinv) m) (zpMul p m (zpMul p fa dinv)) :=
      zpMul_comm p (zpMul p fa dinv) m
    exact ZpEq_trans
      (ZpEq_trans
        (zpAdd_congr (ZpEq_refl _ ) tailComm)
        (zpSub_mul_add_tail (zpMul p fa dinv) a0 m))
      (ZpEq_symm (zpSub_add_cancel
        (zpMul p (zpMul p fa dinv) m) (zpMul p a0 m)))
  have invTerm :
      ZpEq (zpMul p (zpMul p fa dinv) m) fa := by
    have assoc1 :
        ZpEq (zpMul p (zpMul p fa dinv) m)
          (zpMul p fa (zpMul p dinv m)) :=
      zpMul_assoc p fa dinv m
    have rightInv :
        ZpEq (zpMul p dinv m) (zpOne p d.prime) := by
      exact ZpEq_trans (zpMul_right_congr (ZpEq_symm (zpEval_deriv_linear b m a0)))
        (ZpUnitInv_mul_right d (linearHenselUnit b m a0 unit))
    exact ZpEq_trans assoc1
      (ZpEq_trans (zpMul_right_congr rightInv)
        (zpOne_mul_right p fa.prime fa))
  exact ZpEq_trans mulRoot
    (ZpEq_trans subTail (zpSub_congr (ZpEq_refl _) invTerm))

theorem linearHenselRoot_is_root {p : BHist}
    (b m a0 : ZpInt p) (unit : ZpUnit m) :
    ZpEq (zpEval (zpLinearPoly b m) (linearHenselRoot b m a0 unit))
      (zpZero p b.prime) := by
  let fa := zpAdd p b (zpMul p a0 m)
  let r := linearHenselRoot b m a0 unit
  have evalR :
      ZpEq (zpEval (zpLinearPoly b m) r) (zpAdd p b (zpMul p r m)) :=
    zpEval_linear b m r
  have rootMul := linearHenselRoot_mul_slope b m a0 unit
  have replaceMul :
      ZpEq (zpAdd p b (zpMul p r m))
        (zpAdd p b (zpSub p (zpMul p a0 m) fa)) :=
    zpAdd_congr (ZpEq_refl b) rootMul
  have commuteInside :
      ZpEq (zpAdd p b (zpSub p (zpMul p a0 m) fa))
        (zpAdd p (zpSub p (zpMul p a0 m) fa) b) :=
    zpAdd_comm p b (zpSub p (zpMul p a0 m) fa)
  have addBack :
      ZpEq (zpAdd p (zpSub p (zpMul p a0 m) fa) b)
        (zpSub p (zpMul p a0 m) (zpMul p a0 m)) := by
    apply zpAdd_cancel_right (z := zpMul p a0 m)
    have leftAssoc :
        ZpEq
          (zpAdd p
            (zpAdd p (zpSub p (zpMul p a0 m) fa) b)
            (zpMul p a0 m))
          (zpAdd p (zpSub p (zpMul p a0 m) fa)
            (zpAdd p b (zpMul p a0 m))) :=
      zpAdd_assoc p (zpSub p (zpMul p a0 m) fa) b (zpMul p a0 m)
    have closeLeft :
        ZpEq
          (zpAdd p (zpSub p (zpMul p a0 m) fa)
            (zpAdd p b (zpMul p a0 m)))
          (zpMul p a0 m) :=
      ZpEq_trans (zpAdd_congr (ZpEq_refl _)
        (ZpEq_symm (ZpEq_refl fa)))
        (zpSub_add_cancel fa (zpMul p a0 m))
    have rightCancel :
        ZpEq
          (zpAdd p (zpSub p (zpMul p a0 m) (zpMul p a0 m))
            (zpMul p a0 m))
          (zpMul p a0 m) :=
      zpSub_add_cancel (zpMul p a0 m) (zpMul p a0 m)
    exact ZpEq_trans leftAssoc
      (ZpEq_trans closeLeft (ZpEq_symm rightCancel))
  exact ZpEq_trans evalR
    (ZpEq_trans replaceMul
      (ZpEq_trans commuteInside
        (ZpEq_trans addBack (zpSub_self_eq_zero (zpMul p a0 m)))))

end BEDC.Derived.PadicUp
