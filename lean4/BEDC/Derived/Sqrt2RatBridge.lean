import BEDC.Derived.Sqrt2ConvergenceComplete

namespace BEDC.Derived.Sqrt2RatBridge

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp
open BEDC.Derived.RationalUp
open BEDC.Derived.NonCollapseInvariantUp
open BEDC.Derived.Sqrt2BisectionUp
open BEDC.Derived.Sqrt2ConvergenceComplete

def ratFromNatPow (num : Nat) (pow : Nat) : RatNum :=
  natOverPowTwo num pow

def sqrt2LoRat (k : Nat) : RatNum :=
  sqrt2BisectIntervalLo (sqrt2BisectRaw k)

def sqrt2HiRat (k : Nat) : RatNum :=
  sqrt2BisectIntervalHi (sqrt2BisectRaw k)

def sqrt2DyadicUnit (k : Nat) : RatNum :=
  ratFromNatPow 1 k

theorem sqrt2RatBridge_pow_two_cofinal_nat :
    forall threshold : Nat, exists k : Nat, threshold <= powTwoNat k :=
  sqrt2PowTwoNat_cofinal_nat

theorem sqrt2RatBridge_depth_width_bracket (k : Nat) :
    (sqrt2BisectRaw k).depth = k /\
      (sqrt2BisectRaw k).hiNum = (sqrt2BisectRaw k).loNum + 1 /\
        Sqrt2NatBracket (sqrt2BisectRaw k) :=
  sqrt2Bisect_depth_width_bracket k

private theorem natHist_one_intEq :
    IntEq (intOfNat (natHist 1) (natHist_unary 1)) intOne := by
  unfold natHist intOne intOfNat
  exact IntEq_refl _

private theorem positive_int_sign_b0 {z : RatInt} :
    intLe intZero z -> IntNonzero z -> z.sign = BMark.b0 := by
  intro zNonneg zNonzero
  cases z with
  | mk sign magnitude carrier =>
      cases sign with
      | b0 =>
          rfl
      | b1 =>
          have lenLe :
              bwordLength magnitude <= bwordLength BHist.Empty := by
            unfold intLe intZero intOfNat intToPair at zNonneg
            have len :=
              (BEDC.Derived.IntUp.pairLe_iff_length_order
                ⟨unary_empty, unary_empty⟩
                ⟨unary_empty, carrier.right⟩).mp zNonneg
            rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left] at len
            rw [Nat.zero_add, Nat.add_zero] at len
            exact len
          have magLenZero : bwordLength magnitude = 0 := by
            rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left] at lenLe
            exact Nat.eq_zero_of_le_zero lenLe
          have magPos : 0 < bwordLength magnitude :=
            intApart0_length_pos (x := { sign := BMark.b1, magnitude := magnitude, carrier := carrier })
              zNonzero
          rw [magLenZero] at magPos
          cases magPos

private theorem positive_rat_num_sign_b0 {b : RatNum} :
    ratLt ratZero b -> b.num.sign = BMark.b0 := by
  intro hb
  exact positive_int_sign_b0
    (ratNonneg_num (ratLt_to_ratLe hb))
    (ratPositive_num_nonzero hb)

private theorem positive_rat_num_magnitude_pos {b : RatNum} :
    ratLt ratZero b -> 0 < bwordLength b.num.magnitude := by
  intro hb
  exact intApart0_length_pos (ratPositive_num_nonzero hb)

private theorem intLt_nat_of_length_lt {a b : BHist}
    (ha : UnaryHistory a) (hb : UnaryHistory b) :
    bwordLength a < bwordLength b ->
      intLtUp (intOfNat a ha) (intOfNat b hb) := by
  intro hlt
  unfold intLtUp intLt intOfNat intToPair
  change bwordLength a < bwordLength b + 0
  rw [Nat.add_zero]
  exact hlt

private theorem dyadic_left_cross_eq (b : RatNum) (k : Nat) :
    IntEq
      (IntMul (sqrt2DyadicUnit k).num (ratDenInt b))
      (ratDenInt b) := by
  unfold sqrt2DyadicUnit ratFromNatPow natOverPowTwo
  exact IntEq_trans
    (intMul_right_congr natHist_one_intEq)
    (intMul_one_left (ratDenInt b))

private theorem dyadic_right_cross_eq {b : RatNum} (k : Nat)
    (hb : ratLt ratZero b) :
    IntEq
      (IntMul b.num (ratDenInt (sqrt2DyadicUnit k)))
      (intOfNat
        (natMulFn b.num.magnitude (natHist (powTwoNat k)))
        (natMulFn_unary b.num.carrier.right (natHist_unary (powTwoNat k)))) := by
  have signEq : b.num.sign = BMark.b0 := positive_rat_num_sign_b0 hb
  cases b with
  | mk num den den_pos =>
      cases num with
      | mk sign magnitude carrier =>
          cases sign with
          | b0 =>
              unfold sqrt2DyadicUnit ratFromNatPow natOverPowTwo ratDenInt
              exact intMul_same_sign_nat BMark.b0
                magnitude (natHist (powTwoNat k))
                carrier.right (natHist_unary (powTwoNat k))
          | b1 =>
              cases signEq

theorem sqrt2Rat_archimedean_pow_two (b : RatNum) :
    ratLt ratZero b ->
      exists k : Nat, ratLt (sqrt2DyadicUnit k) b := by
  intro hb
  cases sqrt2PowTwoNat_cofinal_nat (bwordLength b.den + 1) with
  | intro k hk =>
      refine ⟨k, ?_⟩
      have denLtPow : bwordLength b.den < powTwoNat k :=
        Nat.lt_of_succ_le hk
      have magPos : 0 < bwordLength b.num.magnitude :=
        positive_rat_num_magnitude_pos hb
      have powLeProduct :
          powTwoNat k <= bwordLength b.num.magnitude * powTwoNat k := by
        calc
          powTwoNat k = 1 * powTwoNat k := (Nat.one_mul (powTwoNat k)).symm
          _ <= bwordLength b.num.magnitude * powTwoNat k :=
            Nat.mul_le_mul_right (powTwoNat k) (Nat.succ_le_of_lt magPos)
      have denLtProduct :
          bwordLength b.den <
            bwordLength b.num.magnitude * powTwoNat k :=
        Nat.lt_of_lt_of_le denLtPow powLeProduct
      have productLength :
          bwordLength
              (natMulFn b.num.magnitude (natHist (powTwoNat k))) =
            bwordLength b.num.magnitude * powTwoNat k := by
        rw [natMulFn_bwordLength b.num.carrier.right (natHist_unary (powTwoNat k))]
        rw [natHist_length]
      have baseLt :
          intLtUp (ratDenInt b)
            (intOfNat
              (natMulFn b.num.magnitude (natHist (powTwoNat k)))
              (natMulFn_unary b.num.carrier.right
                (natHist_unary (powTwoNat k)))) := by
        unfold ratDenInt
        apply intLt_nat_of_length_lt
        rw [productLength]
        exact denLtProduct
      exact intLt_respects
        (IntEq_symm (dyadic_left_cross_eq b k))
        (IntEq_symm (dyadic_right_cross_eq (b := b) k hb))
        baseLt

def sqrt2RatBridge_invariant_from_apart_all
    (apart : Sqrt2BisectApartAllRationals) :
    BoxStreamNonCollapseInvariant sqrt2BisectGauge sqrt2BisectBoxStream :=
  sqrt2_inhabits_NonCollapseInvariant_from_apart_all apart

def sqrt2RatBridge_witness_from_apart_all
    (apart : Sqrt2BisectApartAllRationals) :
    BoxStreamNonCollapseWitness :=
  sqrt2BisectBoxStreamWitness_from_apart_all apart

theorem sqrt2RatBridge_no_exact_rat_retraction_from_apart_all
    (apart : Sqrt2BisectApartAllRationals) :
    BoxStreamExactRatRetraction sqrt2BisectGauge sqrt2BisectBoxStream -> False :=
  sqrt2Bisect_no_exact_rat_retraction_from_apart_all apart

structure Sqrt2RatBridgeArchimedeanStack where
  rat_archimedean :
    forall b : RatNum, ratLt ratZero b ->
      exists k : Nat, ratLt (sqrt2DyadicUnit k) b
  depth_width_bracket :
    forall k : Nat,
      (sqrt2BisectRaw k).depth = k /\
        (sqrt2BisectRaw k).hiNum = (sqrt2BisectRaw k).loNum + 1 /\
          Sqrt2NatBracket (sqrt2BisectRaw k)
  bridge_invariant :
    Sqrt2BisectApartAllRationals ->
      BoxStreamNonCollapseInvariant sqrt2BisectGauge sqrt2BisectBoxStream
  bridge_witness :
    Sqrt2BisectApartAllRationals -> BoxStreamNonCollapseWitness
  bridge_no_retraction :
    Sqrt2BisectApartAllRationals ->
      BoxStreamExactRatRetraction sqrt2BisectGauge sqrt2BisectBoxStream -> False

def sqrt2RatBridge_archimedean_stack : Sqrt2RatBridgeArchimedeanStack :=
  { rat_archimedean := sqrt2Rat_archimedean_pow_two
    depth_width_bracket := sqrt2RatBridge_depth_width_bracket
    bridge_invariant := sqrt2RatBridge_invariant_from_apart_all
    bridge_witness := sqrt2RatBridge_witness_from_apart_all
    bridge_no_retraction := sqrt2RatBridge_no_exact_rat_retraction_from_apart_all }

end BEDC.Derived.Sqrt2RatBridge
