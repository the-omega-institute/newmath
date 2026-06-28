import BEDC.Derived.Sqrt2ApartComplete

namespace BEDC.Derived.Sqrt2ConvergenceComplete

open BEDC.Derived.RationalUp
open BEDC.Derived.NonCollapseInvariantUp
open BEDC.Derived.Sqrt2BisectionUp
open BEDC.Derived.Sqrt2IrrationalUp
open BEDC.Derived.Sqrt2NonCollapseWitnessFinal
open BEDC.Derived.Sqrt2ApartComplete
open BEDC.Derived.RationalSquareOrderUp

theorem powTwoNat_self_covers (threshold : Nat) :
    threshold <= powTwoNat threshold := by
  induction threshold with
  | zero =>
      exact Nat.zero_le _
  | succ threshold ih =>
      change Nat.succ threshold <= 2 * powTwoNat threshold
      have stepToPow :
          Nat.succ threshold <= Nat.succ (powTwoNat threshold) :=
        Nat.succ_le_succ ih
      have powStep :
          Nat.succ (powTwoNat threshold) <= 2 * powTwoNat threshold := by
        rw [Nat.two_mul]
        change powTwoNat threshold + 1 <=
          powTwoNat threshold + powTwoNat threshold
        exact Nat.add_le_add_left
          (powTwoNat_pos threshold) (powTwoNat threshold)
      exact Nat.le_trans stepToPow powStep

theorem sqrt2PowTwoNat_cofinal_nat (threshold : Nat) :
    exists k : Nat, threshold <= powTwoNat k :=
  Exists.intro threshold (powTwoNat_self_covers threshold)

theorem sqrt2Bisect_depth_width_bracket (k : Nat) :
    (sqrt2BisectRaw k).depth = k /\
      (sqrt2BisectRaw k).hiNum = (sqrt2BisectRaw k).loNum + 1 /\
        Sqrt2NatBracket (sqrt2BisectRaw k) := by
  constructor
  · exact sqrt2BisectRaw_depth k
  · constructor
    · exact sqrt2Bisect_width_num_one k
    · exact sqrt2Bisect_lo_sq_lt_two_lt_hi_sq k

theorem sqrt2Bisect_successor_diameter_contract (k : Nat) :
    (sqrt2BisectRaw (Nat.succ k)).hiNum =
        (sqrt2BisectRaw (Nat.succ k)).loNum + 1 /\
      powTwoNat (Nat.succ k) = 2 * powTwoNat k :=
  sqrt2Bisect_diam_halves k

theorem sqrt2Bisect_rational_square_strict_gap (q : RatNum) :
    ratLt (ratMul q q) BEDC.Derived.BoxStreamSqrt2Up.ratTwo \/
      ratLt BEDC.Derived.BoxStreamSqrt2Up.ratTwo (ratMul q q) :=
  sqrt2_rational_square_strict_gap q

theorem sqrt2Bisect_exact_square_absurd (q : RatNum) :
    RatEq (ratMul q q) BEDC.Derived.BoxStreamSqrt2Up.ratTwo -> False :=
  sqrt2Bisect_exact_square_branch_absurd q

def sqrt2BisectBoxStreamWitness_from_apart_all
    (apart : Sqrt2BisectApartAllRationals) :
    BoxStreamNonCollapseWitness :=
  sqrt2BisectWitness_of_apart_all apart

def sqrt2_inhabits_NonCollapseInvariant_from_apart_all
    (apart : Sqrt2BisectApartAllRationals) :
    BoxStreamNonCollapseInvariant sqrt2BisectGauge sqrt2BisectBoxStream :=
  sqrt2Bisect_nonCollapseInvariant_of_apart_all apart

theorem sqrt2Bisect_no_exact_rat_retraction_from_apart_all
    (apart : Sqrt2BisectApartAllRationals) :
    BoxStreamExactRatRetraction sqrt2BisectGauge sqrt2BisectBoxStream -> False :=
  sqrt2Bisect_no_exact_rat_retraction_of_apart_all apart

structure Sqrt2BisectConditionalBridgeStack where
  pow_cofinal_nat : forall threshold : Nat, exists k : Nat, threshold <= powTwoNat k
  depth_width_bracket :
    forall k : Nat,
      (sqrt2BisectRaw k).depth = k /\
        (sqrt2BisectRaw k).hiNum = (sqrt2BisectRaw k).loNum + 1 /\
          Sqrt2NatBracket (sqrt2BisectRaw k)
  square_gap :
    forall q : RatNum,
      ratLt (ratMul q q) BEDC.Derived.BoxStreamSqrt2Up.ratTwo \/
        ratLt BEDC.Derived.BoxStreamSqrt2Up.ratTwo (ratMul q q)
  bridge_witness :
    Sqrt2BisectApartAllRationals -> BoxStreamNonCollapseWitness
  bridge_invariant :
    Sqrt2BisectApartAllRationals ->
      BoxStreamNonCollapseInvariant sqrt2BisectGauge sqrt2BisectBoxStream
  bridge_no_retraction :
    Sqrt2BisectApartAllRationals ->
      BoxStreamExactRatRetraction sqrt2BisectGauge sqrt2BisectBoxStream -> False

def sqrt2Bisect_conditional_bridge_stack : Sqrt2BisectConditionalBridgeStack :=
  { pow_cofinal_nat := sqrt2PowTwoNat_cofinal_nat
    depth_width_bracket := sqrt2Bisect_depth_width_bracket
    square_gap := sqrt2Bisect_rational_square_strict_gap
    bridge_witness := sqrt2BisectBoxStreamWitness_from_apart_all
    bridge_invariant := sqrt2_inhabits_NonCollapseInvariant_from_apart_all
    bridge_no_retraction := sqrt2Bisect_no_exact_rat_retraction_from_apart_all }

end BEDC.Derived.Sqrt2ConvergenceComplete
