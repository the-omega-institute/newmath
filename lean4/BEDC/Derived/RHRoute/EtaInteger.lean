import BEDC.Derived.RHRoute.GroundedAltConvergence
import BEDC.Derived.LocatedTranscendental
import BEDC.Derived.LocatedReal.GroundedDyadic

set_option maxHeartbeats 1000000

namespace BEDC.Derived.RHRoute.AltConvergence

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.RationalUp
open BEDC.Derived.LocatedReal
open BEDC.Derived.LocatedTranscendental

private theorem unary_hsame_of_length {h k : BHist} :
    UnaryHistory h -> UnaryHistory k -> bwordLength h = bwordLength k ->
      hsame h k := by
  intro hUnary kUnary lengthEq
  exact (NatUp_unary_standard_bridge.right.right.right.left hUnary kUnary).mpr lengthEq

private theorem natToUnary_pos_den {n : Nat} :
    0 < n ->
      NatUnaryStrictPrefix BEDC.Derived.PadicUp.NatOne (natToUnary n) ∨
        hsame (natToUnary n) BEDC.Derived.PadicUp.NatOne := by
  intro h
  cases n with
  | zero =>
      cases h
  | succ n =>
      cases n with
      | zero =>
          exact Or.inr rfl
      | succ n =>
          apply Or.inl
          apply BEDC.Derived.PadicUp.NatUnaryStrictPrefix_of_length_lt
          · exact unary_e1_closed unary_empty
          · exact natToUnary_unary (Nat.succ (Nat.succ n))
          · rw [NatUp_unary_standard_bridge.right.left BHist.Empty unary_empty]
            rw [natToUnary_length]
            exact Nat.succ_lt_succ (Nat.zero_lt_succ n)

private theorem natPow_pos (base e : Nat) :
    0 < base -> 0 < base ^ e := by
  intro h
  induction e with
  | zero =>
      exact Nat.succ_pos 0
  | succ e ih =>
      change 0 < base ^ e * base
      exact Nat.mul_pos ih h

private theorem natPow_mono_base {x y e : Nat} :
    x <= y -> x ^ e <= y ^ e := by
  intro h
  induction e with
  | zero =>
      exact Nat.le_refl 1
  | succ e ih =>
      change x ^ e * x <= y ^ e * y
      exact Nat.mul_le_mul ih h

private theorem natPow_one_le {base e : Nat} :
    1 <= base -> 1 <= base ^ e := by
  intro hbase
  induction e with
  | zero =>
      exact Nat.le_refl 1
  | succ e ih =>
      change 1 <= base ^ e * base
      calc
        1 = 1 * 1 := rfl
        _ <= base ^ e * base := Nat.mul_le_mul ih hbase

private theorem natPow_self_le_pow {base e : Nat} :
    1 <= base -> 1 <= e -> base <= base ^ e := by
  intro hbase he
  cases e with
  | zero =>
      cases he
  | succ e =>
      change base <= base ^ e * base
      calc
        base = 1 * base := (Nat.one_mul base).symm
        _ <= base ^ e * base := Nat.mul_le_mul_right base (natPow_one_le hbase)

private theorem powTwoNat_mono {i j : Nat} :
    i <= j -> powTwoNat i <= powTwoNat j := by
  intro h
  induction h with
  | refl =>
      exact Nat.le_refl _
  | @step j _ ih =>
      have stepLe : powTwoNat j <= 2 * powTwoNat j := by
        have raw : 1 * powTwoNat j <= 2 * powTwoNat j :=
          Nat.mul_le_mul_right (powTwoNat j) (Nat.succ_le_succ (Nat.zero_le 1))
        rw [Nat.one_mul] at raw
        exact raw
      exact Nat.le_trans ih stepLe

def etaIntDen (s n : Nat) : Nat :=
  (n + 1) ^ s

theorem etaIntDen_pos (s n : Nat) :
    0 < etaIntDen s n := by
  unfold etaIntDen
  exact natPow_pos (n + 1) s (Nat.succ_pos n)

private def unitNatTerm (d : Nat) (hd : 0 < d) : RatNum :=
  { num := intOne
    den := natToUnary d
    den_pos := natToUnary_pos_den hd }

def etaIntTerm (s : Nat) (n : Nat) : RatNum :=
  unitNatTerm (etaIntDen s n) (etaIntDen_pos s n)

private theorem etaIntTerm_nonneg (s n : Nat) :
    ratLe ratZero (etaIntTerm s n) := by
  apply ratNonneg_of_num
  unfold etaIntTerm unitNatTerm intOne
  exact intLe_zero_of_nat BEDC.Derived.PadicUp.NatOne
    (unary_e1_closed unary_empty)

private theorem unitNatTerm_le_of_den_ge {d e : Nat} (hd : 0 < d) (he : 0 < e) :
    e <= d -> ratLe (unitNatTerm d hd) (unitNatTerm e he) := by
  intro hden
  unfold ratLe unitNatTerm ratDenInt
  change
    intLe
      (IntMul intOne (intOfNat (natToUnary e)
        (ratDenCarrier
          { num := intOne
            den := natToUnary e
            den_pos := natToUnary_pos_den he })))
      (IntMul intOne (intOfNat (natToUnary d)
        (ratDenCarrier
          { num := intOne
            den := natToUnary d
            den_pos := natToUnary_pos_den hd })))
  have leftOne :
      IntEq
        (IntMul intOne (intOfNat (natToUnary e)
          (ratDenCarrier
            { num := intOne
              den := natToUnary e
              den_pos := natToUnary_pos_den he })))
        (intOfNat (natToUnary e) (natToUnary_unary e)) := by
    exact IntEq_trans
      (intMul_one_left
        (intOfNat (natToUnary e)
          (ratDenCarrier
            { num := intOne
              den := natToUnary e
              den_pos := natToUnary_pos_den he })))
      (intOfNat_hsame_congr
        (ratDenCarrier
          { num := intOne
            den := natToUnary e
            den_pos := natToUnary_pos_den he })
        (natToUnary_unary e)
        (hsame_refl _))
  have rightOne :
      IntEq
        (IntMul intOne (intOfNat (natToUnary d)
          (ratDenCarrier
            { num := intOne
              den := natToUnary d
              den_pos := natToUnary_pos_den hd })))
        (intOfNat (natToUnary d) (natToUnary_unary d)) := by
    exact IntEq_trans
      (intMul_one_left
        (intOfNat (natToUnary d)
          (ratDenCarrier
            { num := intOne
              den := natToUnary d
              den_pos := natToUnary_pos_den hd })))
      (intOfNat_hsame_congr
        (ratDenCarrier
          { num := intOne
            den := natToUnary d
            den_pos := natToUnary_pos_den hd })
        (natToUnary_unary d)
        (hsame_refl _))
  exact intLe_respects (IntEq_symm leftOne) (IntEq_symm rightOne)
    (BEDC.Derived.LocatedReal.intOfNat_le_of_nat_le
      (natToUnary e) (natToUnary d)
      (natToUnary_unary e) (natToUnary_unary d)
      (by
        rw [natToUnary_length, natToUnary_length]
        exact hden))

private theorem etaIntTerm_le_of_den_ge {s m n : Nat} :
    etaIntDen s n <= etaIntDen s m ->
      ratLe (etaIntTerm s m) (etaIntTerm s n) := by
  intro h
  exact unitNatTerm_le_of_den_ge (etaIntDen_pos s m) (etaIntDen_pos s n) h

theorem etaIntTerm_antitone (s : Nat) (_hs : 1 <= s) (n : Nat) :
    ratLe (etaIntTerm s (n + 1)) (etaIntTerm s n) := by
  apply etaIntTerm_le_of_den_ge
  unfold etaIntDen
  exact natPow_mono_base (e := s) (Nat.succ_le_succ (Nat.le_succ n))

private theorem etaIntTerm_le_unit (s : Nat) (hs : 1 <= s) (n : Nat) :
    ratLe (etaIntTerm s n) (unitNatTerm (n + 1) (Nat.succ_pos n)) := by
  exact unitNatTerm_le_of_den_ge (etaIntDen_pos s n) (Nat.succ_pos n)
    (by
      unfold etaIntDen
      exact natPow_self_le_pow (Nat.succ_pos n) hs)

private theorem unitFraction_le_dyadic {j n : Nat} :
    powTwoNat j <= n + 1 ->
      ratLe
        (unitNatTerm (n + 1) (Nat.succ_pos n))
        (dyadicRat j) := by
  intro h
  unfold ratLe ratDenInt
  change
    intLe
      (IntMul intOne (ratDenInt (dyadicRat j)))
      (IntMul intOne (intOfNat (natToUnary (n + 1))
        (ratDenCarrier
          { num := intOne
            den := natToUnary (n + 1)
            den_pos := natToUnary_pos_den (Nat.succ_pos n) })))
  have leftOne :
      IntEq
        (IntMul intOne (ratDenInt (dyadicRat j)))
        (intOfNat (natToUnary (powTwoNat j)) (natToUnary_unary (powTwoNat j))) := by
    exact IntEq_trans
      (BEDC.Derived.RationalUp.IntMul_respects (IntEq_refl intOne) (ratDenInt_dyadic j))
      (intMul_one_left _)
  have rightOne :
      IntEq
        (IntMul intOne (intOfNat (natToUnary (n + 1))
          (ratDenCarrier
            { num := intOne
              den := natToUnary (n + 1)
              den_pos := natToUnary_pos_den (Nat.succ_pos n) })))
        (intOfNat (natToUnary (n + 1)) (natToUnary_unary (n + 1))) := by
    exact IntEq_trans
      (intMul_one_left
        (intOfNat (natToUnary (n + 1))
          (ratDenCarrier
            { num := intOne
              den := natToUnary (n + 1)
              den_pos := natToUnary_pos_den (Nat.succ_pos n) })))
      (intOfNat_hsame_congr
        (ratDenCarrier
          { num := intOne
            den := natToUnary (n + 1)
            den_pos := natToUnary_pos_den (Nat.succ_pos n) })
        (natToUnary_unary (n + 1))
        (hsame_refl _))
  exact intLe_respects (IntEq_symm leftOne) (IntEq_symm rightOne)
    (BEDC.Derived.LocatedReal.intOfNat_le_of_nat_le
      (natToUnary (powTwoNat j)) (natToUnary (n + 1))
      (natToUnary_unary (powTwoNat j)) (natToUnary_unary (n + 1))
      (by
        rw [natToUnary_length, natToUnary_length]
        exact h))

private theorem etaIntTerm_zeroSpec (s : Nat) (hs : 1 <= s) :
    ∀ k n : Nat, powTwoNat k <= n -> ratLe (etaIntTerm s n) (dyadicRat k) := by
  intro k n hn
  exact ratLe_trans (etaIntTerm_le_unit s hs n)
    (unitFraction_le_dyadic (Nat.le_trans hn (Nat.le_succ n)))

def etaIntLeibniz (s : Nat) (hs : 1 <= s) : RatLeibnizData :=
  { a := etaIntTerm s
    nonneg := etaIntTerm_nonneg s
    antitone := etaIntTerm_antitone s hs
    zeroIndex := fun j => powTwoNat j
    zeroIndex_mono := by
      intro i j hij
      exact powTwoNat_mono hij
    zeroSpec := etaIntTerm_zeroSpec s hs }

def etaIntLimit (s : Nat) (hs : 1 <= s) :
    LReal (RatToleranceMetricKit groundedRatToleranceLaws) :=
  groundedAltLimit (etaIntLeibniz s hs)

end BEDC.Derived.RHRoute.AltConvergence
