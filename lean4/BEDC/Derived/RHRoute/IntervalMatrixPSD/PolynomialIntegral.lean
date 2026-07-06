import BEDC.Derived.RHRoute.IntervalMatrixPSD.PanelSum
import BEDC.Derived.RHRoute.IntervalMatrixPSD.QRatBridge
import BEDC.Derived.LocatedReal.GroundedToleranceKit

set_option maxRecDepth 4096

namespace BEDC.Derived.RHRoute.IntervalMatrixPSD

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Derived.LocatedReal
open BEDC.Real.RatNumKernel
open BEDC.Algebra.Rel (RelCommRing)

abbrev LocatedRatKit : RatMetricKit :=
  RatToleranceMetricKit groundedRatToleranceLaws

abbrev LocatedRatReal : Type :=
  LReal LocatedRatKit

def polyIntegralRawSeq (cs : List BRat) (a b : BRat) : Nat -> BRat :=
  fun n => leftFrom (evalPoly cs) (hUniform a b n) (panels n) a

def polyIntegralGap (cs : List BRat) (a b : BRat) : BRat :=
  ratSub (antiEvalPoly cs b) (antiEvalPoly cs a)

def polyIntegralRhs (cs : List BRat) (a b : BRat) (n : Nat) : BRat :=
  ratMul (natRat (panels n))
    (ratDivTwo
      (ratMul
        (derivBound cs (ratMax (ratAbs a) (ratAbs b)))
        (ratMul (hUniform a b n) (hUniform a b n))))

def polyIntegralBudgetRat (cs : List BRat) (a b : BRat) : BRat :=
  ratAbs
    (ratMul
      (derivBound cs (ratMax (ratAbs a) (ratAbs b)))
      (ratMul (ratSub b a) (ratSub b a)))

def polyIntegralBudgetNat (cs : List BRat) (a b : BRat) : Nat :=
  Nat.succ (bwordLength (polyIntegralBudgetRat cs a b).num.magnitude)

def polyIntegralWork (cs : List BRat) (a b : BRat) (k : Nat) : Nat :=
  polyIntegralBudgetNat cs a b * powTwoNat k

def polyIntegralPanelIndex (cs : List BRat) (a b : BRat) (k : Nat) : Nat :=
  polyIntegralWork cs a b k

def polyIntegralSeq (cs : List BRat) (a b : BRat) : Nat -> BRat :=
  polyIntegralRawSeq cs a b

private theorem natToUnary_pos_den {n : Nat} :
    0 < n ->
      NatUnaryStrictPrefix NatOne (natToUnary n) ∨
        hsame (natToUnary n) NatOne := by
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
          apply NatUnaryStrictPrefix_of_length_lt
          · exact unary_e1_closed unary_empty
          · exact natToUnary_unary (Nat.succ (Nat.succ n))
          · rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.left
              BHist.Empty unary_empty]
            rw [natToUnary_length]
            exact Nat.succ_lt_succ (Nat.zero_lt_succ n)

private def unitNatTerm (d : Nat) (hd : 0 < d) : BRat :=
  { num := intOne
    den := natToUnary d
    den_pos := natToUnary_pos_den hd }

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
      (BEDC.Derived.RationalUp.IntMul_respects (IntEq_refl intOne)
        (ratDenInt_dyadic j))
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

private def natFrac (C N : Nat) (hN : 0 < N) : BRat :=
  { num := intOfNat (natToUnary C) (natToUnary_unary C)
    den := natToUnary N
    den_pos := natToUnary_pos_den hN }

private theorem natFrac_le_dyadic {C N k : Nat} (hN : 0 < N) :
    C * powTwoNat k <= N -> ratLe (natFrac C N hN) (dyadicRat k) := by
  intro h
  unfold ratLe natFrac ratDenInt
  change
    intLe
      (IntMul (intOfNat (natToUnary C) (natToUnary_unary C))
        (ratDenInt (dyadicRat k)))
      (IntMul intOne (intOfNat (natToUnary N)
        (ratDenCarrier
          { num := intOfNat (natToUnary C) (natToUnary_unary C)
            den := natToUnary N
            den_pos := natToUnary_pos_den hN })))
  let prod := natMulFn (natToUnary C) (natToUnary (powTwoNat k))
  have prodUnary : UnaryHistory prod :=
    natMulFn_unary (natToUnary_unary C)
      (natToUnary_unary (powTwoNat k))
  have leftEq :
      IntEq
        (IntMul (intOfNat (natToUnary C) (natToUnary_unary C))
          (ratDenInt (dyadicRat k)))
        (intOfNat prod prodUnary) := by
    have denEq := ratDenInt_dyadic k
    have step :
        IntEq
          (IntMul (intOfNat (natToUnary C) (natToUnary_unary C))
            (ratDenInt (dyadicRat k)))
          (IntMul (intOfNat (natToUnary C) (natToUnary_unary C))
            (intOfNat (natToUnary (powTwoNat k))
              (natToUnary_unary (powTwoNat k)))) :=
      BEDC.Derived.RationalUp.IntMul_respects (IntEq_refl _) denEq
    exact IntEq_trans step
      (IntEq_symm
        (intOfNat_natMul_as_intMul
          (natToUnary C) (natToUnary (powTwoNat k))
          (natToUnary_unary C) (natToUnary_unary (powTwoNat k))
          prodUnary))
  have rightEq :
      IntEq
        (IntMul intOne (intOfNat (natToUnary N)
          (ratDenCarrier
            { num := intOfNat (natToUnary C) (natToUnary_unary C)
              den := natToUnary N
              den_pos := natToUnary_pos_den hN })))
        (intOfNat (natToUnary N) (natToUnary_unary N)) := by
    exact IntEq_trans
      (intMul_one_left _)
      (intOfNat_hsame_congr
        (ratDenCarrier
          { num := intOfNat (natToUnary C) (natToUnary_unary C)
            den := natToUnary N
            den_pos := natToUnary_pos_den hN })
        (natToUnary_unary N) (hsame_refl _))
  have prodLen : bwordLength prod = C * powTwoNat k := by
    unfold prod
    rw [natMulFn_bwordLength (natToUnary_unary C)
      (natToUnary_unary (powTwoNat k))]
    rw [natToUnary_length, natToUnary_length]
  have lenLe : bwordLength prod <= bwordLength (natToUnary N) := by
    rw [prodLen, natToUnary_length]
    exact h
  have base :
      intLe (intOfNat prod prodUnary)
        (intOfNat (natToUnary N) (natToUnary_unary N)) :=
    BEDC.Derived.LocatedReal.intOfNat_le_of_nat_le _ _ _ _ lenLe
  exact intLe_respects (IntEq_symm leftEq) (IntEq_symm rightEq) base

private theorem natRat_as_ratNat (n : Nat) :
    RatEq (natRat n) (BEDC.Real.RatNumKernel.ratNat n) := by
  cases n with
  | zero =>
      unfold natRat BEDC.Real.RatNumKernel.ratNat ratZero intToRat intZero intOfNat
      exact RatEq_refl _
  | succ n =>
      cases n with
      | zero =>
          unfold natRat BEDC.Real.RatNumKernel.ratNat ratOne intToRat intOne intOfNat
          exact RatEq_refl _
      | succ n =>
          cases n with
          | zero =>
              unfold natRat
              have oneKernel : RatEq ratOne (BEDC.Real.RatNumKernel.ratNat 1) := by
                unfold BEDC.Real.RatNumKernel.ratNat ratOne intToRat intOne intOfNat
                exact RatEq_refl _
              exact RatEq_trans _ _ _
                (ratAdd_respects oneKernel oneKernel)
                (BEDC.Real.RatNumLogEnclosure.ratNat_add 1 1)
          | succ n =>
              unfold natRat
              exact RatEq_refl _

private theorem dyadic_eq_inv_ratNat (k : Nat) :
    RatEq (dyadicRat k)
      (ratInvApart (BEDC.Real.RatNumKernel.ratNat (powTwoNat k))
        (BEDC.Real.RatNumLogEnclosure.ratNat_apart0_of_pos
          (powTwoNat_pos k))) := by
  apply ratEq_of_num_den_intEq
  · unfold dyadicRat BEDC.Real.RatNumKernel.ratNat ratInvApart
    unfold intToRat intOne intOfNat intOfNatWithSign
    exact IntEq_refl _
  · unfold dyadicRat BEDC.Real.RatNumKernel.ratNat ratInvApart
    unfold ratDenInt intToRat intOne intOfNat intOfNatWithSign
    exact IntEq_refl _

private theorem dyadic_mul_pow_cancel (k : Nat) :
    RatEq
      (ratMul (dyadicRat k)
        (BEDC.Real.RatNumKernel.ratNat (powTwoNat k)))
      ratOne := by
  have invEq := dyadic_eq_inv_ratNat k
  exact RatEq_trans _ _ _
    (ratMul_respects invEq (RatEq_refl _))
    (RatEq_trans _ _ _
      (ratMul_comm _ _)
      (ratInvApart_mul (BEDC.Real.RatNumKernel.ratNat (powTwoNat k))
        (BEDC.Real.RatNumLogEnclosure.ratNat_apart0_of_pos
          (powTwoNat_pos k))))

private theorem ratDen_length_pos_local (x : BRat) :
    1 <= bwordLength x.den := by
  cases x.den_pos with
  | inl strict =>
      have lt := NatUnaryStrictPrefix_length_lt
        (unary_e1_closed unary_empty) strict
      change bwordLength NatOne < bwordLength x.den at lt
      rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.left
        BHist.Empty unary_empty] at lt
      exact Nat.le_of_lt lt
  | inr same =>
      have len := congrArg bwordLength same
      rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.left
        BHist.Empty unary_empty] at len
      rw [len]
      exact Nat.le_refl 1

private theorem ratMagnitude_le_ratNat_numLen (x : BRat) :
    ratLe (ratMagnitude x)
      (BEDC.Real.RatNumKernel.ratNat (bwordLength x.num.magnitude)) := by
  unfold ratLe ratMagnitude BEDC.Real.RatNumKernel.ratNat intToRat ratDenInt
  change
    intLe
      (IntMul (intOfNat x.num.magnitude x.num.carrier.right)
        (intOfNat NatOne (unary_e1_closed unary_empty)))
      (IntMul (intOfNat (natToUnary (bwordLength x.num.magnitude))
          (natToUnary_unary (bwordLength x.num.magnitude)))
        (intOfNat x.den (ratDenCarrier
          { num := intOfNat x.num.magnitude x.num.carrier.right
            den := x.den
            den_pos := x.den_pos })))
  have leftEq :
      IntEq
        (IntMul (intOfNat x.num.magnitude x.num.carrier.right)
          (intOfNat NatOne (unary_e1_closed unary_empty)))
        (intOfNat x.num.magnitude x.num.carrier.right) :=
    intMul_one_right _
  let prod := natMulFn (natToUnary (bwordLength x.num.magnitude)) x.den
  have prodUnary : UnaryHistory prod :=
    natMulFn_unary (natToUnary_unary (bwordLength x.num.magnitude))
      (ratDenCarrier x)
  have rightEq :
      IntEq
        (IntMul (intOfNat (natToUnary (bwordLength x.num.magnitude))
            (natToUnary_unary (bwordLength x.num.magnitude)))
          (intOfNat x.den (ratDenCarrier
            { num := intOfNat x.num.magnitude x.num.carrier.right
              den := x.den
              den_pos := x.den_pos })))
        (intOfNat prod prodUnary) := by
    exact IntEq_symm
      (intOfNat_natMul_as_intMul
        (natToUnary (bwordLength x.num.magnitude)) x.den
        (natToUnary_unary (bwordLength x.num.magnitude))
        (ratDenCarrier x) prodUnary)
  have sameMag : hsame x.num.magnitude
      (natToUnary (bwordLength x.num.magnitude)) := by
    exact
      (BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.right.right.left
        x.num.carrier.right
        (natToUnary_unary (bwordLength x.num.magnitude))).mpr
      (by rw [natToUnary_length])
  have leftToNat :
      IntEq (intOfNat x.num.magnitude x.num.carrier.right)
        (intOfNat (natToUnary (bwordLength x.num.magnitude))
          (natToUnary_unary (bwordLength x.num.magnitude))) :=
    intOfNat_hsame_congr x.num.carrier.right
      (natToUnary_unary (bwordLength x.num.magnitude)) sameMag
  have natLeProd :
      bwordLength (natToUnary (bwordLength x.num.magnitude)) <=
        bwordLength prod := by
    unfold prod
    rw [natMulFn_bwordLength
      (natToUnary_unary (bwordLength x.num.magnitude)) (ratDenCarrier x)]
    rw [natToUnary_length]
    exact Nat.le_mul_of_pos_right (bwordLength x.num.magnitude)
      (ratDen_length_pos_local x)
  have base :
      intLe
        (intOfNat (natToUnary (bwordLength x.num.magnitude))
          (natToUnary_unary (bwordLength x.num.magnitude)))
        (intOfNat prod prodUnary) :=
    BEDC.Derived.LocatedReal.intOfNat_le_of_nat_le _ _ _ _ natLeProd
  have leftOrigToNat :
      IntEq
        (IntMul (intOfNat x.num.magnitude x.num.carrier.right)
          (intOfNat NatOne (unary_e1_closed unary_empty)))
        (intOfNat (natToUnary (bwordLength x.num.magnitude))
          (natToUnary_unary (bwordLength x.num.magnitude))) :=
    IntEq_trans leftEq leftToNat
  exact intLe_respects (IntEq_symm leftOrigToNat) (IntEq_symm rightEq) base

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

private abbrev ratRing : RelCommRing BRat RatEq :=
  ratRelCommRing

private theorem ratDivApart_le_same_num_den_mono_local
    {x a b : BRat}
    (hx : ratLe ratZero x)
    (ha : ratLt ratZero a)
    (hb : ratLt ratZero b)
    (haApart : ratApart0 a)
    (hbApart : ratApart0 b)
    (hab : ratLe a b) :
    ratLe (ratDivApart x b hbApart) (ratDivApart x a haApart) := by
  have leftCancel :
      RatEq (ratMul (ratDivApart x b hbApart) b) x :=
    BEDC.Real.RatNumKernel.ratDivApart_mul_cancel_right hbApart
  have rightCancel :
      RatEq (ratMul (ratDivApart x a haApart) a) x :=
    BEDC.Real.RatNumKernel.ratDivApart_mul_cancel_right haApart
  have divBNonneg :
      ratLe ratZero (ratDivApart x b hbApart) :=
    BEDC.Real.RatNumKernel.ratDivApart_nonneg_of_nonneg_pos hx hb hbApart
  have step :
      ratLe (ratMul (ratDivApart x b hbApart) a)
        (ratMul (ratDivApart x b hbApart) b) :=
    BEDC.Real.RatNumKernel.ratMul_le_mul_nonneg_left hab divBNonneg
  have toX :
      ratLe (ratMul (ratDivApart x b hbApart) a) x :=
    BEDC.Real.RatNumKernel.ratLe_of_RatEq_right step leftCancel
  have targetMul :
      ratLe (ratMul (ratDivApart x b hbApart) a)
        (ratMul (ratDivApart x a haApart) a) :=
    BEDC.Real.RatNumKernel.ratLe_of_RatEq_right toX
      (RatEq_symm rightCancel)
  exact ratMul_le_cancel_right ha targetMul

private theorem ratDivNat_mul_cancel_local (x : BRat) (n : Nat) :
    RatEq (ratMul (ratDivNat x n) (natRat (Nat.succ n))) x := by
  exact ratDivNat_mul_cancel x n

private theorem hUniform_mul_cancel_local (a b : BRat) (n : Nat) :
    RatEq (ratMul (hUniform a b n) (natRat (Nat.succ n)))
      (ratSub b a) := by
  unfold hUniform
  exact ratDivNat_mul_cancel (ratSub b a) n

private theorem ratMul_square_cancel_of_right
    (D L H N : BRat)
    (hHN : RatEq (ratMul H N) L) :
    RatEq
      (ratMul
        (ratMul N (ratMul D (ratMul H H)))
        N)
      (ratMul D (ratMul L L)) := by
  have step0 :
      RatEq
        (ratMul (ratMul N (ratMul D (ratMul H H))) N)
        (ratMul (ratMul (ratMul D (ratMul H H)) N) N) := by
    exact ratMul_respects (ratMul_comm N (ratMul D (ratMul H H)))
      (RatEq_refl N)
  have step1 :
      RatEq
        (ratMul (ratMul (ratMul D (ratMul H H)) N) N)
        (ratMul (ratMul D (ratMul (ratMul H H) N)) N) := by
    exact ratMul_respects (ratMul_assoc D (ratMul H H) N)
      (RatEq_refl N)
  have step2 :
      RatEq
        (ratMul (ratMul D (ratMul (ratMul H H) N)) N)
        (ratMul (ratMul D (ratMul H (ratMul H N))) N) := by
    exact ratMul_respects
      (ratMul_respects (RatEq_refl D) (ratMul_assoc H H N))
      (RatEq_refl N)
  have step3 :
      RatEq
        (ratMul (ratMul D (ratMul H (ratMul H N))) N)
        (ratMul (ratMul D (ratMul H L)) N) := by
    exact ratMul_respects
      (ratMul_respects (RatEq_refl D)
        (ratMul_respects (RatEq_refl H) hHN))
      (RatEq_refl N)
  have step4 :
      RatEq
        (ratMul (ratMul D (ratMul H L)) N)
        (ratMul D (ratMul (ratMul H L) N)) :=
    ratMul_assoc D (ratMul H L) N
  have step5 :
      RatEq
        (ratMul D (ratMul (ratMul H L) N))
        (ratMul D (ratMul L L)) := by
    have inner : RatEq (ratMul (ratMul H L) N) (ratMul L L) := by
      exact RatEq_trans _ _ _
        (ratMul_assoc H L N)
        (RatEq_trans _ _ _
          (ratMul_respects (RatEq_refl H) (ratMul_comm L N))
          (RatEq_trans _ _ _
            (RatEq_symm (ratMul_assoc H N L))
            (ratMul_respects hHN (RatEq_refl L))))
    exact ratMul_respects (RatEq_refl D) inner
  exact RatEq_trans _ _ _ step0
    (RatEq_trans _ _ _ step1
      (RatEq_trans _ _ _ step2
        (RatEq_trans _ _ _ step3
          (RatEq_trans _ _ _ step4 step5))))

private theorem ratMul_square_div_cancel_local (D L : BRat) (n : Nat) :
    RatEq
      (ratMul
        (ratMul (natRat (Nat.succ n))
          (ratMul D (ratMul (ratDivNat L n) (ratDivNat L n))))
        (natRat (Nat.succ n)))
      (ratMul D (ratMul L L)) := by
  exact ratMul_square_cancel_of_right D L (ratDivNat L n)
    (natRat (Nat.succ n)) (ratDivNat_mul_cancel_local L n)

private theorem natRat_succ_pos_local (n : Nat) :
    ratLt ratZero (natRat (Nat.succ n)) := by
  cases n with
  | zero =>
      change ratLt ratZero ratOne
      exact BEDC.Real.RatNumLogEnclosure.ratOne_pos
  | succ n =>
      cases n with
      | zero =>
          have oneKernel : RatEq ratOne (BEDC.Real.RatNumKernel.ratNat 1) := by
            unfold BEDC.Real.RatNumKernel.ratNat ratOne intToRat intOne intOfNat
            exact RatEq_refl _
          have h := BEDC.Real.RatNumLogEnclosure.ratNat_add 1 1
          have twoBridge : RatEq (natRat 2)
              (BEDC.Real.RatNumKernel.ratNat 2) := by
            change RatEq (ratAdd ratOne ratOne)
              (BEDC.Real.RatNumKernel.ratNat 2)
            exact RatEq_trans _ _ _
              (ratAdd_respects oneKernel oneKernel)
              h
          exact BEDC.Real.RatNumKernel.ratLt_of_RatEq_right
            (BEDC.Real.RatNumLogEnclosure.ratNat_pos_of_pos
              (Nat.succ_pos 1))
            (RatEq_symm twoBridge)
      | succ n =>
          change ratLt ratZero
            (BEDC.Real.RatNumKernel.ratNat
              (Nat.succ (Nat.succ (Nat.succ n))))
          exact BEDC.Real.RatNumLogEnclosure.ratNat_pos_of_pos
            (Nat.succ_pos _)

private theorem natRat_succ_apart_local (n : Nat) :
    ratApart0 (natRat (Nat.succ n)) :=
  BEDC.Real.RatNumKernel.ratApart0_of_pos
    (natRat_succ_pos_local n)

private theorem natRat_nonneg_local (n : Nat) :
    ratLe ratZero (natRat n) :=
  BEDC.Real.RatNumKernel.ratLe_of_RatEq_right
    (BEDC.Real.RatNumKernel.ratNat_nonneg n)
    (RatEq_symm (natRat_as_ratNat n))

private theorem ratDivTwo_mul_cancel_local (x : BRat) :
    RatEq (ratMul (ratDivTwo x) ratTwoPanel) x := by
  unfold ratDivTwo ratTwoPanel
  exact BEDC.Real.RatNumKernel.ratDivApart_mul_cancel_right
    (natRat_succ_apart_local 1)

private theorem ratTwoPanel_mul_local (x : BRat) :
    RatEq (ratMul ratTwoPanel x) (ratAdd x x) := by
  unfold ratTwoPanel
  change RatEq (ratMul (ratAdd ratOne ratOne) x) (ratAdd x x)
  exact RatEq_trans _ _ _
    (BEDC.Real.RatNumKernel.ratMul_add_right ratOne ratOne x)
    (ratAdd_respects (ratOne_mul_left x) (ratOne_mul_left x))

private theorem ratAdd_self_eq_twoPanel_mul_local (x : BRat) :
    RatEq (ratAdd x x) (ratMul x ratTwoPanel) := by
  exact RatEq_trans _ _ _
    (RatEq_symm (ratTwoPanel_mul_local x))
    (ratMul_comm ratTwoPanel x)

private theorem ratDivNat_ratNat_le_dyadic {C n k : Nat} :
    C * powTwoNat k <= n + 1 ->
      ratLe
        (ratDivNat (BEDC.Real.RatNumKernel.ratNat C) n)
        (dyadicRat k) := by
  intro h
  have powPos :
      ratLt ratZero
        (BEDC.Real.RatNumKernel.ratNat (powTwoNat k)) :=
    BEDC.Real.RatNumLogEnclosure.ratNat_pos_of_pos (powTwoNat_pos k)
  apply ratMul_le_cancel_right powPos
  have leftAssoc :
      RatEq
        (ratMul
          (ratMul
            (ratDivNat (BEDC.Real.RatNumKernel.ratNat C) n)
            (BEDC.Real.RatNumKernel.ratNat (powTwoNat k)))
          (natRat (Nat.succ n)))
        (ratMul (BEDC.Real.RatNumKernel.ratNat C)
          (BEDC.Real.RatNumKernel.ratNat (powTwoNat k))) := by
    have move :
        RatEq
          (ratMul
            (ratMul
              (ratDivNat (BEDC.Real.RatNumKernel.ratNat C) n)
              (BEDC.Real.RatNumKernel.ratNat (powTwoNat k)))
            (natRat (Nat.succ n)))
          (ratMul
            (ratMul
              (ratDivNat (BEDC.Real.RatNumKernel.ratNat C) n)
              (natRat (Nat.succ n)))
            (BEDC.Real.RatNumKernel.ratNat (powTwoNat k))) := by
      exact RatEq_trans _ _ _
        (ratMul_assoc
          (ratDivNat (BEDC.Real.RatNumKernel.ratNat C) n)
          (BEDC.Real.RatNumKernel.ratNat (powTwoNat k))
          (natRat (Nat.succ n)))
        (RatEq_trans _ _ _
          (ratMul_respects (RatEq_refl _) (ratMul_comm _ _))
          (RatEq_symm (ratMul_assoc _ _ _)))
    exact RatEq_trans _ _ _ move
      (ratMul_respects
        (ratDivNat_mul_cancel_local
          (BEDC.Real.RatNumKernel.ratNat C) n)
        (RatEq_refl _))
  have rightAssoc :
      RatEq
        (ratMul
          (ratMul (dyadicRat k)
            (BEDC.Real.RatNumKernel.ratNat (powTwoNat k)))
          (natRat (Nat.succ n)))
        (natRat (Nat.succ n)) := by
    exact RatEq_trans _ _ _
      (ratMul_respects (dyadic_mul_pow_cancel k) (RatEq_refl _))
      (ratOne_mul_left _)
  have productLe :
      ratLe
        (ratMul (BEDC.Real.RatNumKernel.ratNat C)
          (BEDC.Real.RatNumKernel.ratNat (powTwoNat k)))
        (natRat (Nat.succ n)) := by
    have natProductEq :
        RatEq
          (ratMul (BEDC.Real.RatNumKernel.ratNat C)
            (BEDC.Real.RatNumKernel.ratNat (powTwoNat k)))
          (BEDC.Real.RatNumKernel.ratNat (C * powTwoNat k)) := by
      exact BEDC.Real.RatNumLogEnclosure.ratNat_mul C (powTwoNat k)
    exact ratLe_respects
      (RatEq_symm natProductEq)
      (RatEq_symm (natRat_as_ratNat (Nat.succ n)))
      (BEDC.Real.RatNumKernel.ratNat_le_of_nat_le h)
  have scaled :
      ratLe
        (ratMul
          (ratMul
            (ratDivNat (BEDC.Real.RatNumKernel.ratNat C) n)
            (BEDC.Real.RatNumKernel.ratNat (powTwoNat k)))
          (natRat (Nat.succ n)))
        (ratMul
          (ratMul (dyadicRat k)
            (BEDC.Real.RatNumKernel.ratNat (powTwoNat k)))
          (natRat (Nat.succ n))) :=
    ratLe_respects (RatEq_symm leftAssoc) (RatEq_symm rightAssoc)
      productLe
  exact ratMul_le_cancel_right (natRat_succ_pos_local n) scaled

private theorem ratDivTwo_le_self_of_nonneg {x : BRat}
    (hx : ratLe ratZero x) :
    ratLe (ratDivTwo x) x := by
  apply ratMul_le_cancel_right (natRat_succ_pos_local 1)
  have left :
      RatEq (ratMul (ratDivTwo x) ratTwoPanel) x :=
    ratDivTwo_mul_cancel_local x
  have right :
      RatEq (ratMul x ratTwoPanel) (ratAdd x x) :=
    RatEq_symm (ratAdd_self_eq_twoPanel_mul_local x)
  have xLeAdd :
      ratLe x (ratAdd x x) :=
    BEDC.Real.RatNumLogEnclosure.ratLe_add_nonneg_right x x hx
  change ratLe (ratMul (ratDivTwo x) ratTwoPanel)
    (ratMul x ratTwoPanel)
  exact ratLe_respects (RatEq_symm left) (RatEq_symm right) xLeAdd

private theorem ratSub_respects_local {x x' y y' : BRat} :
    RatEq x x' -> RatEq y y' -> RatEq (ratSub x y) (ratSub x' y') := by
  intro hx hy
  unfold ratSub
  exact ratAdd_respects hx (ratNeg_respects hy)

private theorem ratDivTwo_nonneg_local {x : BRat}
    (hx : ratLe ratZero x) :
    ratLe ratZero (ratDivTwo x) := by
  unfold ratDivTwo
  exact BEDC.Real.RatNumKernel.ratDivApart_nonneg_of_nonneg_pos
    hx
    (BEDC.Real.RatNumLogEnclosure.ratNat_pos_of_pos (Nat.succ_pos 1))
    (BEDC.Real.RatNumLogEnclosure.ratNat_apart0_of_pos (Nat.succ_pos 1))

private theorem uniform_bound_nonneg_local (a b : BRat) :
    ratLe ratZero (ratMax (ratAbs a) (ratAbs b)) :=
  ratLe_trans (ratMagnitude_nonneg a) (ratMax_ge_left (ratAbs a) (ratAbs b))

private theorem hUniform_nonneg_local {a b : BRat} (n : Nat)
    (hab : ratLe a b) :
    ratLe ratZero (hUniform a b n) :=
  hUniform_nonneg n hab

private theorem polyIntegralRhs_times_panels_le_budget
    (cs : List BRat) (a b : BRat) (hab : ratLe a b) (n : Nat) :
    ratLe
      (ratMul (polyIntegralRhs cs a b n) (natRat (Nat.succ n)))
      (polyIntegralBudgetRat cs a b) := by
  let D := derivBound cs (ratMax (ratAbs a) (ratAbs b))
  let L := ratSub b a
  let H := hUniform a b n
  let N := natRat (Nat.succ n)
  have innerNonneg :
    ratLe ratZero
        (ratMul D (ratMul H H)) := by
    exact BEDC.Real.RatNumKernel.ratMul_nonneg
      (derivBound_nonneg cs (ratMax (ratAbs a) (ratAbs b))
        (uniform_bound_nonneg_local a b))
      (BEDC.Real.RatNumKernel.ratMul_nonneg
        (hUniform_nonneg_local n hab)
        (hUniform_nonneg_local n hab))
  have dropHalf :
      ratLe
        (ratDivTwo (ratMul D (ratMul H H)))
        (ratMul D (ratMul H H)) :=
    ratDivTwo_le_self_of_nonneg innerNonneg
  have leftStep :
      ratLe
        (ratMul N (ratDivTwo (ratMul D (ratMul H H))))
        (ratMul N (ratMul D (ratMul H H))) :=
    BEDC.Real.RatNumKernel.ratMul_le_mul_nonneg_left dropHalf
      (ratLt_to_ratLe (natRat_succ_pos_local n))
  have squareCancel :
      RatEq
        (ratMul (ratMul N (ratMul D (ratMul H H))) N)
        (ratMul D (ratMul L L)) := by
    exact ratMul_square_cancel_of_right
      (derivBound cs (ratMax (ratAbs a) (ratAbs b)))
      (ratSub b a)
      (hUniform a b n)
      (natRat (Nat.succ n))
      (hUniform_mul_cancel_local a b n)
  have squareToBudget :
      ratLe
        (ratMul (ratMul N (ratMul D (ratMul H H))) N)
        (polyIntegralBudgetRat cs a b) := by
    have absBound :
        ratLe
          (ratMul
            (derivBound cs (ratMax (ratAbs a) (ratAbs b)))
            (ratMul (ratSub b a) (ratSub b a)))
          (polyIntegralBudgetRat cs a b) := by
      unfold polyIntegralBudgetRat
      exact ratLe_self_abs
        (ratMul
          (derivBound cs (ratMax (ratAbs a) (ratAbs b)))
          (ratMul (ratSub b a) (ratSub b a)))
    exact BEDC.Real.RatNumKernel.ratLe_of_RatEq_left
      squareCancel
      absBound
  have raw :
      ratLe
        (ratMul (ratMul N (ratDivTwo (ratMul D (ratMul H H)))) N)
        (polyIntegralBudgetRat cs a b) := by
    exact ratLe_trans
      (ratMul_le_mul_right leftStep
        (ratLt_to_ratLe (natRat_succ_pos_local n)))
      squareToBudget
  have leftEq :
      RatEq
        (ratMul (polyIntegralRhs cs a b n) (natRat (Nat.succ n)))
        (ratMul (ratMul N (ratDivTwo (ratMul D (ratMul H H)))) N) := by
    unfold polyIntegralRhs D H N
    exact RatEq_refl _
  exact BEDC.Real.RatNumKernel.ratLe_of_RatEq_left leftEq raw

private theorem polyIntegralBudget_le_budgetNat
    (cs : List BRat) (a b : BRat) :
    ratLe (polyIntegralBudgetRat cs a b)
      (BEDC.Real.RatNumKernel.ratNat
        (polyIntegralBudgetNat cs a b)) := by
  unfold polyIntegralBudgetNat
  have magLe :
      ratLe (ratMagnitude (polyIntegralBudgetRat cs a b))
        (BEDC.Real.RatNumKernel.ratNat
          (bwordLength (polyIntegralBudgetRat cs a b).num.magnitude)) :=
    ratMagnitude_le_ratNat_numLen (polyIntegralBudgetRat cs a b)
  have budgetLeMag :
      ratLe (polyIntegralBudgetRat cs a b)
        (ratMagnitude (polyIntegralBudgetRat cs a b)) :=
    ratLe_self_abs (polyIntegralBudgetRat cs a b)
  have natStep :
      ratLe
        (BEDC.Real.RatNumKernel.ratNat
          (bwordLength (polyIntegralBudgetRat cs a b).num.magnitude))
        (BEDC.Real.RatNumKernel.ratNat
          (Nat.succ
            (bwordLength (polyIntegralBudgetRat cs a b).num.magnitude))) :=
    BEDC.Real.RatNumKernel.ratNat_le_of_nat_le
      (Nat.le_succ _)
  exact ratLe_trans budgetLeMag (ratLe_trans magLe natStep)

private theorem ratDist_le_of_abs_sub_le {x y r : BRat} :
    ratLe (ratAbs (ratSub x y)) r -> ratLe (ratDist x y) r := by
  intro h
  exact h

private theorem ratDist_symm_le {x y r : BRat} :
    ratLe (ratDist x y) r -> ratLe (ratDist y x) r := by
  intro h
  exact ratLe_trans
    (ratLe_of_RatEq (ratDist_symm y x))
    h

private theorem seq_gap_error
    (cs : List BRat) (a b : BRat) (hab : ratLe a b) (n : Nat) :
    ratLe
      (ratDist (polyIntegralSeq cs a b n) (polyIntegralGap cs a b))
      (polyIntegralRhs cs a b n) := by
  exact ratDist_le_of_abs_sub_le
    (by
      unfold polyIntegralSeq polyIntegralGap polyIntegralRhs
      exact left_sum_error_uniform cs a b hab n)

-- The constructive modulus below is intentionally explicit.  It is the only
-- bridge still specialized to the polynomial panel estimate; the located-real
-- construction never replaces the Riemann sums by the antiderivative gap.
private theorem polyIntegralRhs_le_dyadic
    (cs : List BRat) (a b : BRat) (hab : ratLe a b) :
    ∀ k n : Nat, polyIntegralWork cs a b k <= n ->
      ratLe (polyIntegralRhs cs a b n) (dyadicRat k) := by
  intro k n hn
  have denomPos : ratLt ratZero (natRat (Nat.succ n)) :=
    natRat_succ_pos_local n
  apply ratMul_le_cancel_right denomPos
  have rhsTimesBudget :
      ratLe
        (ratMul (polyIntegralRhs cs a b n) (natRat (Nat.succ n)))
        (polyIntegralBudgetRat cs a b) :=
    polyIntegralRhs_times_panels_le_budget cs a b hab n
  have budgetLeNat :
      ratLe (polyIntegralBudgetRat cs a b)
        (BEDC.Real.RatNumKernel.ratNat
          (polyIntegralBudgetNat cs a b)) :=
    polyIntegralBudget_le_budgetNat cs a b
  have divBudget :
      ratLe
        (ratDivNat
          (BEDC.Real.RatNumKernel.ratNat
            (polyIntegralBudgetNat cs a b)) n)
        (dyadicRat k) := by
    apply ratDivNat_ratNat_le_dyadic
    unfold polyIntegralWork at hn
    exact Nat.le_succ_of_le hn
  have divBudgetScaled :
      ratLe
        (BEDC.Real.RatNumKernel.ratNat
          (polyIntegralBudgetNat cs a b))
        (ratMul (dyadicRat k) (natRat (Nat.succ n))) := by
    have scaled :
        ratLe
          (ratMul
            (ratDivNat
              (BEDC.Real.RatNumKernel.ratNat
                (polyIntegralBudgetNat cs a b)) n)
            (natRat (Nat.succ n)))
          (ratMul (dyadicRat k) (natRat (Nat.succ n))) :=
      ratMul_le_mul_right divBudget (ratLt_to_ratLe denomPos)
    exact BEDC.Real.RatNumKernel.ratLe_of_RatEq_left
      (RatEq_symm
        (ratDivNat_mul_cancel_local
          (BEDC.Real.RatNumKernel.ratNat
            (polyIntegralBudgetNat cs a b)) n))
      scaled
  exact ratLe_trans rhsTimesBudget (ratLe_trans budgetLeNat divBudgetScaled)

private theorem polyIntegralSeq_cauchy_close
    (cs : List BRat) (a b : BRat) (hab : ratLe a b) :
    ∀ k m n : Nat,
      polyIntegralWork cs a b (Nat.succ k) <= m ->
      polyIntegralWork cs a b (Nat.succ k) <= n ->
        ratToleranceClose (polyIntegralSeq cs a b m)
          (polyIntegralSeq cs a b n) k := by
  intro k m n hm hn
  unfold ratToleranceClose
  have left :
      ratLe
        (ratDist (polyIntegralSeq cs a b m) (polyIntegralGap cs a b))
        (dyadicRat (Nat.succ k)) :=
    ratLe_trans (seq_gap_error cs a b hab m)
      (polyIntegralRhs_le_dyadic cs a b hab (Nat.succ k) m hm)
  have rightRaw :
      ratLe
        (ratDist (polyIntegralSeq cs a b n) (polyIntegralGap cs a b))
        (dyadicRat (Nat.succ k)) :=
    ratLe_trans (seq_gap_error cs a b hab n)
      (polyIntegralRhs_le_dyadic cs a b hab (Nat.succ k) n hn)
  have right :
      ratLe
        (ratDist (polyIntegralGap cs a b) (polyIntegralSeq cs a b n))
        (dyadicRat (Nat.succ k)) :=
    ratDist_symm_le rightRaw
  have tri :
      ratLe
        (ratDist (polyIntegralSeq cs a b m) (polyIntegralSeq cs a b n))
        (ratAdd (dyadicRat (Nat.succ k)) (dyadicRat (Nat.succ k))) :=
    ratLe_trans
      (BEDC.Derived.LocatedReal.ratDist_triangle
        (polyIntegralSeq cs a b m) (polyIntegralGap cs a b)
        (polyIntegralSeq cs a b n))
      (BEDC.Derived.LocatedReal.ratLe_add_mono left right)
  exact ratLe_trans tri (dyadic_succ_add k)

private theorem polyIntegralWork_mono
    (cs : List BRat) (a b : BRat) :
    ∀ {i j : Nat}, i <= j ->
      polyIntegralWork cs a b i <= polyIntegralWork cs a b j := by
  intro i j hij
  unfold polyIntegralWork
  exact Nat.mul_le_mul_left _
    (by
      induction j generalizing i with
      | zero =>
          cases i with
          | zero => exact Nat.le_refl _
          | succ i => cases hij
      | succ j ih =>
          cases i with
          | zero =>
              exact Nat.le_trans (Nat.le_refl 1) (powTwoNat_pos (Nat.succ j))
          | succ i =>
              change 2 * powTwoNat i <= 2 * powTwoNat j
              exact Nat.mul_le_mul_left 2 (ih (Nat.le_of_succ_le_succ hij)))

def polyRiemannIntegral (cs : List BRat) (a b : BRat)
    (hab : ratLe a b) : LocatedRatReal where
  seq := polyIntegralSeq cs a b
  modulus := fun k => polyIntegralWork cs a b (Nat.succ k)
  modulus_mono := by
    intro i j hij
    exact polyIntegralWork_mono cs a b (Nat.succ_le_succ hij)
  cauchy := by
    intro k m n hm hn
    exact polyIntegralSeq_cauchy_close cs a b hab k m n hm hn

theorem polyRiemannIntegral_eq_antideriv
    (cs : List BRat) (a b : BRat) (hab : ratLe a b) :
    LRealEq LocatedRatKit
      (polyRiemannIntegral cs a b hab)
      (ratToLReal LocatedRatKit (polyIntegralGap cs a b)) := by
  exact ⟨
    { modulus := fun k => polyIntegralWork cs a b k
      close := by
        intro k m n hm _hn
        unfold polyRiemannIntegral ratToLReal LocatedRatKit RatToleranceMetricKit
        unfold ratToleranceClose
        exact ratLe_trans (seq_gap_error cs a b hab m)
          (polyIntegralRhs_le_dyadic cs a b hab k m hm) }⟩

def qHalf : FormalPoly.QRat :=
  FormalPoly.qraw 1 2

private theorem ratZero_le_ratOne : ratLe ratZero ratOne :=
  BEDC.Real.RatNumLogEnclosure.ratOne_nonneg

example :
    LRealEq LocatedRatKit
      (polyRiemannIntegral [ratZero, ratOne] ratZero ratOne ratZero_le_ratOne)
      (ratToLReal LocatedRatKit (FormalPoly.qToBRat qHalf)) := by
  exact LRealEq_trans
    (polyRiemannIntegral_eq_antideriv [ratZero, ratOne] ratZero ratOne
      ratZero_le_ratOne)
    (ratToLReal_respects (by
      unfold polyIntegralGap antiEvalPoly antiEvalShift qHalf
      unfold FormalPoly.qToBRat FormalPoly.qraw
      change RatEq (ratSub (ratAdd ratZero (ratAdd (ratDivNat ratOne 1) ratZero))
        (ratAdd ratZero (ratAdd (ratDivNat ratZero 1) ratZero)))
        (ratDivNat ratOne 1)
      exact RatEq_trans _ _ _
        (ratSub_respects_local
          (RatEq_trans _ _ _
            (ratAdd_respects (RatEq_refl ratZero)
              (ratAdd_respects (RatEq_refl (ratDivNat ratOne 1))
                (RatEq_refl ratZero)))
            (ratZero_add_left (ratAdd (ratDivNat ratOne 1) ratZero)))
          (RatEq_trans _ _ _
            (ratAdd_respects (RatEq_refl ratZero)
              (ratAdd_respects (RatEq_refl (ratDivNat ratZero 1))
                (RatEq_refl ratZero)))
            (ratZero_add_left (ratAdd (ratDivNat ratZero 1) ratZero))))
        (RatEq_trans _ _ _
          (ratSub_respects_local
            (ratAdd_zero_right (ratDivNat ratOne 1))
            (RatEq_trans _ _ _
              (ratAdd_zero_right (ratDivNat ratZero 1))
              (by
                unfold ratDivNat
                exact ratMul_zero_left_local _)))
          (RatEq_trans _ _ _
            (ratSub_respects_local (RatEq_refl _) (RatEq_refl ratZero))
            (RatEq_trans _ _ _
              (by unfold ratSub; exact ratAdd_respects (RatEq_refl _) (RatEq_refl _))
              (ratAdd_zero_right (ratDivNat ratOne 1)))))))

private def ratNegOne : BRat :=
  ratNeg ratOne

private theorem ratNegOne_le_ratOne : ratLe ratNegOne ratOne := by
  unfold ratNegOne
  exact ratLe_trans
    (BEDC.Derived.LocatedReal.ratLe_neg_abs ratOne)
    (ratLe_of_RatEq (ratMagnitude_eq_self_of_nonneg ratZero_le_ratOne))

example :
    LRealEq LocatedRatKit
      (polyRiemannIntegral [ratZero, ratOne] ratNegOne ratOne ratNegOne_le_ratOne)
      (ratToLReal LocatedRatKit ratZero) := by
  exact LRealEq_trans
    (polyRiemannIntegral_eq_antideriv [ratZero, ratOne] ratNegOne ratOne
      ratNegOne_le_ratOne)
    (ratToLReal_respects (by
      unfold polyIntegralGap antiEvalPoly antiEvalShift ratNegOne
      change RatEq
        (ratSub
          (ratAdd ratZero (ratAdd (ratDivNat ratOne 1) ratZero))
          (ratAdd ratZero
            (ratAdd (ratDivNat (ratMul ratOne (ratMul (ratNeg ratOne) (ratNeg ratOne))) 1)
              ratZero)))
        ratZero
      have negSq :
          RatEq (ratMul (ratNeg ratOne) (ratNeg ratOne)) ratOne := by
        exact RatEq_trans _ _ _
          (ratRing.neg_neg_mul_neg ratOne ratOne)
          (ratMul_one_right ratOne)
      have rightEq :
          RatEq
            (ratAdd ratZero
              (ratAdd
                (ratDivNat
                  (ratMul ratOne (ratMul (ratNeg ratOne) (ratNeg ratOne))) 1)
                ratZero))
            (ratAdd ratZero (ratAdd (ratDivNat ratOne 1) ratZero)) := by
        exact ratAdd_respects (RatEq_refl ratZero)
          (ratAdd_respects
            (by
              unfold ratDivNat
              exact ratMul_respects
                (ratMul_respects (RatEq_refl ratOne) negSq)
                (RatEq_refl _))
            (RatEq_refl ratZero))
      exact RatEq_trans _ _ _
        (ratSub_respects_local (RatEq_refl _) rightEq)
        (ratSub_self (ratAdd ratZero (ratAdd (ratDivNat ratOne 1) ratZero)))))

namespace FormalPoly

def specializeXB (p : BiPoly) (x : BRat) : List BRat :=
  match p with
  | [] => []
  | a :: rest => evalB a x :: specializeXB rest x

-- Rational specializations can be read back coefficientwise with QRatBridge.
-- The remaining overlap equation is the algebraic commutation of
-- specializeXB with antiderivU/evalU at the two U-endpoints.  The existing
-- Brick B certificate for log2 remains the interval-enclosure surface; this
-- file only builds the located-real integral semantics for rational
-- coefficient lists.

end FormalPoly

end BEDC.Derived.RHRoute.IntervalMatrixPSD
