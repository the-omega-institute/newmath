import BEDC.Derived.PellUp
import BEDC.Derived.LucasSequenceUp
import BEDC.Derived.IntUp.Arithmetic

namespace BEDC.Derived.PellLucasUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp

abbrev Z : Type := BEDC.Algebra.Rel.IntegerUp
abbrev Zeq : Z -> Z -> Prop := BEDC.Algebra.Rel.IntEq

def integerRing : BEDC.Algebra.Rel.RelCommRing Z Zeq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

abbrev zzero : Z := integerRing.zero
abbrev zone : Z := integerRing.one
abbrev zadd : Z -> Z -> Z := integerRing.add
abbrev zmul : Z -> Z -> Z := integerRing.mul
abbrev zneg : Z -> Z := integerRing.neg
abbrev zsub : Z -> Z -> Z := integerRing.sub

def intOfNatStd (n : Nat) : Z :=
  BEDC.Derived.RationalUp.intOfNat (natToUnary n) (natToUnary_unary n)

abbrev ztwo : Z := intOfNatStd 2
abbrev pellD : Z := ztwo

def zsq (x : Z) : Z :=
  zmul x x

def pellNumber : Nat -> Z
  | 0 => zzero
  | 1 => zone
  | n + 2 => zadd (zmul ztwo (pellNumber (n + 1))) (pellNumber n)

def companionPell : Nat -> Z
  | 0 => ztwo
  | 1 => ztwo
  | n + 2 => zadd (zmul ztwo (companionPell (n + 1))) (companionPell n)

def pellNat : Nat -> Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * pellNat (n + 1) + pellNat n

def companionPellNat : Nat -> Nat
  | 0 => 2
  | 1 => 2
  | n + 2 => 2 * companionPellNat (n + 1) + companionPellNat n

def pellNormTwo (x y : Z) : Z :=
  BEDC.Derived.PellUp.pellNorm pellD x y

def pellPairFromSequences (n : Nat) : BEDC.Derived.PellUp.PellPair :=
  { x := companionPell n, y := pellNumber n }

theorem pellNumber_zero :
    Zeq (pellNumber 0) zzero := by
  exact integerRing.refl zzero

theorem pellNumber_one :
    Zeq (pellNumber 1) zone := by
  exact integerRing.refl zone

theorem pellNumber_recurrence (n : Nat) :
    Zeq (pellNumber (n + 2))
      (zadd (zmul ztwo (pellNumber (n + 1))) (pellNumber n)) := by
  exact integerRing.refl (pellNumber (n + 2))

theorem companionPell_zero :
    Zeq (companionPell 0) ztwo := by
  exact integerRing.refl ztwo

theorem companionPell_one :
    Zeq (companionPell 1) ztwo := by
  exact integerRing.refl ztwo

theorem companionPell_recurrence (n : Nat) :
    Zeq (companionPell (n + 2))
      (zadd (zmul ztwo (companionPell (n + 1))) (companionPell n)) := by
  exact integerRing.refl (companionPell (n + 2))

theorem pellNat_zero :
    pellNat 0 = 0 := by
  rfl

theorem pellNat_one :
    pellNat 1 = 1 := by
  rfl

theorem pellNat_recurrence (n : Nat) :
    pellNat (n + 2) = 2 * pellNat (n + 1) + pellNat n := by
  rfl

theorem companionPellNat_zero :
    companionPellNat 0 = 2 := by
  rfl

theorem companionPellNat_one :
    companionPellNat 1 = 2 := by
  rfl

theorem companionPellNat_recurrence (n : Nat) :
    companionPellNat (n + 2) =
      2 * companionPellNat (n + 1) + companionPellNat n := by
  rfl

private def twoStep (motive : Nat -> Prop)
    (zeroCase : motive 0)
    (oneCase : motive 1)
    (stepCase : ∀ n, motive n -> motive (n + 1) -> motive (n + 2)) :
    ∀ n, motive n
  | 0 => zeroCase
  | 1 => oneCase
  | n + 2 =>
      stepCase n
        (twoStep motive zeroCase oneCase stepCase n)
        (twoStep motive zeroCase oneCase stepCase (n + 1))

private theorem nat_step_distrib_four (a b c d : Nat) :
    2 * (a + b) + (c + d) = (2 * a + c) + (2 * b + d) := by
  calc
    2 * (a + b) + (c + d)
        = (2 * a + 2 * b) + (c + d) :=
          congrArg (fun x => x + (c + d)) (Nat.mul_add 2 a b)
    _ = 2 * a + (2 * b + (c + d)) :=
          Nat.add_assoc (2 * a) (2 * b) (c + d)
    _ = 2 * a + ((2 * b + c) + d) :=
          congrArg (fun x => 2 * a + x) (Nat.add_assoc (2 * b) c d).symm
    _ = 2 * a + ((c + 2 * b) + d) :=
          congrArg (fun x => 2 * a + (x + d)) (Nat.add_comm (2 * b) c)
    _ = 2 * a + (c + (2 * b + d)) :=
          congrArg (fun x => 2 * a + x) (Nat.add_assoc c (2 * b) d)
    _ = (2 * a + c) + (2 * b + d) :=
          (Nat.add_assoc (2 * a) c (2 * b + d)).symm

theorem companionPellNat_eq_pellNat_adjacent_sum (n : Nat) :
    companionPellNat (n + 1) = pellNat (n + 2) + pellNat n := by
  exact twoStep
    (fun k => companionPellNat (k + 1) = pellNat (k + 2) + pellNat k)
    (by rfl)
    (by rfl)
    (by
      intro k h0 h1
      unfold companionPellNat pellNat
      rw [h1, h0]
      exact nat_step_distrib_four
        (pellNat (k + 3)) (pellNat (k + 1)) (pellNat (k + 2)) (pellNat k))
    n

theorem companionPell_eq_pell_adjacent_sum_at_zero :
    Zeq (companionPell 0) (zadd (pellNumber 1) (pellNumber 1)) := by
  exact integerRing.refl ztwo

theorem companionPell_eq_pell_adjacent_sum_at_one :
    Zeq (companionPell 1) (zadd (pellNumber 2) (pellNumber 0)) := by
  exact integerRing.symm (integerRing.add_zero ztwo)

theorem lucasU_pell_parameters :
    BEDC.Derived.LucasSequenceUp.lucasU 2 (-1) 0 = 0 ∧
      BEDC.Derived.LucasSequenceUp.lucasU 2 (-1) 1 = 1 ∧
      (∀ n : Nat,
        BEDC.Derived.LucasSequenceUp.lucasU 2 (-1) (n + 2) =
          2 * BEDC.Derived.LucasSequenceUp.lucasU 2 (-1) (n + 1) -
            (-1) * BEDC.Derived.LucasSequenceUp.lucasU 2 (-1) n) := by
  exact ⟨rfl, ⟨rfl, fun n => BEDC.Derived.LucasSequenceUp.lucasU_recurrence 2 (-1) n⟩⟩

theorem lucasV_companion_pell_parameters :
    BEDC.Derived.LucasSequenceUp.lucasV 2 (-1) 0 = 2 ∧
      BEDC.Derived.LucasSequenceUp.lucasV 2 (-1) 1 = 2 ∧
      (∀ n : Nat,
        BEDC.Derived.LucasSequenceUp.lucasV 2 (-1) (n + 2) =
          2 * BEDC.Derived.LucasSequenceUp.lucasV 2 (-1) (n + 1) -
            (-1) * BEDC.Derived.LucasSequenceUp.lucasV 2 (-1) n) := by
  exact ⟨rfl, ⟨rfl, fun n => BEDC.Derived.LucasSequenceUp.lucasV_recurrence 2 (-1) n⟩⟩

theorem pellNormTwo_trivial :
    Zeq (pellNormTwo zone zzero) zone :=
  BEDC.Derived.PellUp.pell_trivial_solution pellD

theorem pellEquation_plus_one_trivial :
    Zeq (zsub (zsq zone) (zmul ztwo (zsq zzero))) zone :=
  pellNormTwo_trivial

theorem pellNormTwo_negative_seed :
    Zeq (pellNormTwo zone zone) (zneg zone) := by
  exact integerRing.refl (zneg zone)

theorem pellEquation_minus_one_seed :
    Zeq (zsub (zsq zone) (zmul ztwo (zsq zone))) (zneg zone) :=
  pellNormTwo_negative_seed

theorem pellNormTwo_mul_closed (a b : BEDC.Derived.PellUp.PellPair) :
    Zeq
      (pellNormTwo
        (BEDC.Derived.PellUp.pellPairMul pellD a b).x
        (BEDC.Derived.PellUp.pellPairMul pellD a b).y)
      (zmul (pellNormTwo a.x a.y) (pellNormTwo b.x b.y)) :=
  BEDC.Derived.PellUp.pellNorm_mul pellD a b

theorem pellNormTwo_compose_closed
    (x1 y1 x2 y2 : Z) :
    Zeq
      (pellNormTwo
        (BEDC.Derived.PellUp.pellComposeX pellD x1 y1 x2 y2)
        (BEDC.Derived.PellUp.pellComposeY pellD x1 y1 x2 y2))
      (zmul (pellNormTwo x1 y1) (pellNormTwo x2 y2)) :=
  BEDC.Derived.PellUp.pellNorm_compose pellD x1 y1 x2 y2

theorem pellSolutionGenerated_norm_one (n : Nat) :
    BEDC.Derived.PellUp.IsPellSolution pellD
      (BEDC.Derived.PellUp.pellSolutionGenerated pellD zone zzero
        (BEDC.Derived.PellUp.pell_trivial_solution pellD) n).x
      (BEDC.Derived.PellUp.pellSolutionGenerated pellD zone zzero
        (BEDC.Derived.PellUp.pell_trivial_solution pellD) n).y :=
  BEDC.Derived.PellUp.pellSolutionGenerated_isPell pellD zone zzero
    (BEDC.Derived.PellUp.pell_trivial_solution pellD) n

end BEDC.Derived.PellLucasUp
