import BEDC.Derived.LocatedReal.RatMetricKit

namespace BEDC.Derived.LocatedReal

open BEDC.Derived.RationalUp

def ratToleranceClose (x y : Rat) (k : Nat) : Prop :=
  ratLe (ratDist x y) (dyadicRat k)

structure RatToleranceCloseLaws where
  close_refl : forall x : Rat, forall k : Nat, ratToleranceClose x x k
  close_symm :
    forall {x y : Rat} {k : Nat},
      ratToleranceClose x y k -> ratToleranceClose y x k
  close_weaken :
    forall {x y : Rat} {hi lo : Nat},
      lo <= hi -> ratToleranceClose x y hi -> ratToleranceClose x y lo
  close_triangle :
    forall {x y z : Rat} {k : Nat},
      ratToleranceClose x y (Nat.succ k) ->
        ratToleranceClose y z (Nat.succ k) ->
          ratToleranceClose x z k
  eq_close :
    forall {x y : Rat}, RatEq x y -> forall k : Nat, ratToleranceClose x y k
  add_close :
    forall {x x' y y' : Rat} {k : Nat},
      ratToleranceClose x x' (Nat.succ k) ->
        ratToleranceClose y y' (Nat.succ k) ->
          ratToleranceClose (ratAdd x y) (ratAdd x' y') k
  neg_close :
    forall {x y : Rat} {k : Nat},
      ratToleranceClose x y k ->
        ratToleranceClose (ratNeg x) (ratNeg y) k

structure RatToleranceMetricObligations where
  laws : RatToleranceCloseLaws
  ratDist_triangle :
    forall x y z : Rat,
      ratLe (ratDist x z) (ratAdd (ratDist x y) (ratDist y z))
  dyadic_succ_add :
    forall k : Nat,
      ratLe (ratAdd (dyadicRat (Nat.succ k)) (dyadicRat (Nat.succ k)))
        (dyadicRat k)

def ratToleranceCloseAt (x y : Rat) (k : Nat)
    (_laws : RatToleranceCloseLaws) : Prop :=
  ratToleranceClose x y k

def RatToleranceMetricKit (laws : RatToleranceCloseLaws) : RatMetricKit where
  close := ratToleranceClose
  apart := ratExactApart
  le := RatEq
  close_refl := laws.close_refl
  close_symm := by
    intro x y k
    exact laws.close_symm
  close_weaken := by
    intro x y hi lo
    exact laws.close_weaken
  close_triangle := by
    intro x y z k
    exact laws.close_triangle
  eq_close := by
    intro x y h
    exact laws.eq_close h
  add_close := by
    intro x x' y y' k
    exact laws.add_close
  neg_close := by
    intro x y k
    exact laws.neg_close
  le_refl := RatEq_refl
  le_trans := by
    intro x y z xy yz
    exact RatEq_trans x y z xy yz
  le_antisymm := by
    intro x y xy _yx
    exact xy
  apart_symm := by
    intro x y k
    exact ratExactApart_symm

theorem ratToleranceClose_def (x y : Rat) (k : Nat) :
    ratToleranceClose x y k = ratLe (ratDist x y) (dyadicRat k) := by
  rfl

theorem RatToleranceMetricKit_close
    (laws : RatToleranceCloseLaws) (x y : Rat) (k : Nat) :
    (RatToleranceMetricKit laws).close x y k = ratToleranceClose x y k := by
  rfl

end BEDC.Derived.LocatedReal
