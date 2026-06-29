import BEDC.Derived.RationalOrderArithUp

set_option maxHeartbeats 2000000

namespace BEDC.Real.RatNumKernel

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PadicUp
open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp

abbrev Rat : Type :=
  RatNum

def ratNat (n : Nat) : Rat :=
  intToRat (intOfNat (natToUnary n) (natToUnary_unary n))

def ratPow (x : Rat) : Nat -> Rat
  | 0 => ratOne
  | Nat.succ n => ratMul (ratPow x n) x

def ratSum : Nat -> (Nat -> Rat) -> Rat
  | 0, _ => ratZero
  | Nat.succ n, f => ratAdd (ratSum n f) (f n)

def geomSum (q : Rat) (K : Nat) : Rat :=
  ratSum K (fun j => ratPow q j)

def oddDen (M : Nat) : Rat :=
  ratNat (2 * M + 1)

private theorem intOfNat_le_of_nat_le {m n : Nat} (h : m ≤ n) :
    intLe (intOfNat (natToUnary m) (natToUnary_unary m))
      (intOfNat (natToUnary n) (natToUnary_unary n)) := by
  unfold intLe intOfNat intToPair
  apply pairLe_of_length_order
  · exact ⟨natToUnary_unary m, unary_empty⟩
  · exact ⟨natToUnary_unary n, unary_empty⟩
  rw [natToUnary_length, natToUnary_length]
  rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left]
  rw [Nat.add_zero, Nat.add_zero]
  exact h

theorem ratNat_nonneg (n : Nat) :
    ratLe ratZero (ratNat n) := by
  apply ratNonneg_of_num
  unfold ratNat intToRat
  exact intLe_zero_of_nat (natToUnary n) (natToUnary_unary n)

theorem ratNat_le_of_nat_le {m n : Nat} (h : m ≤ n) :
    ratLe (ratNat m) (ratNat n) := by
  unfold ratLe ratNat
  let mz : RatInt := intOfNat (natToUnary m) (natToUnary_unary m)
  let nz : RatInt := intOfNat (natToUnary n) (natToUnary_unary n)
  change intLe (IntMul mz (ratDenInt (intToRat nz)))
    (IntMul nz (ratDenInt (intToRat mz)))
  have leftOne : IntEq (IntMul mz (ratDenInt (intToRat nz))) mz := by
    have denOne : IntEq (ratDenInt (intToRat nz)) intOne := by
      unfold ratDenInt intToRat intOne
      exact IntEq_refl (intOfNat NatOne (unary_e1_closed unary_empty))
    exact IntEq_trans (intMul_left_congr denOne) (intMul_one_right mz)
  have rightOne : IntEq (IntMul nz (ratDenInt (intToRat mz))) nz := by
    have denOne : IntEq (ratDenInt (intToRat mz)) intOne := by
      unfold ratDenInt intToRat intOne
      exact IntEq_refl (intOfNat NatOne (unary_e1_closed unary_empty))
    exact IntEq_trans (intMul_left_congr denOne) (intMul_one_right nz)
  exact intLe_respects (IntEq_symm leftOne) (IntEq_symm rightOne)
    (intOfNat_le_of_nat_le h)

theorem ratLe_of_RatEq_left {x y z : Rat} :
    RatEq x y -> ratLe y z -> ratLe x z := by
  intro same h
  exact ratLe_respects (RatEq_symm same) (RatEq_refl z) h

theorem ratLe_of_RatEq_right {x y z : Rat} :
    ratLe x y -> RatEq y z -> ratLe x z := by
  intro h same
  exact ratLe_respects (RatEq_refl x) same h

theorem ratLt_of_RatEq_left {x y z : Rat} :
    RatEq x y -> ratLt y z -> ratLt x z := by
  intro same h
  apply ratLe_not_le_to_ratLt
  · exact ratLe_of_RatEq_left same (ratLt_to_ratLe h)
  · intro zx
    exact ratLt_not_ratLe_reverse h
      (ratLe_of_RatEq_right zx same)

theorem ratLt_of_RatEq_right {x y z : Rat} :
    ratLt x y -> RatEq y z -> ratLt x z := by
  intro h same
  apply ratLe_not_le_to_ratLt
  · exact ratLe_of_RatEq_right (ratLt_to_ratLe h) same
  · intro zx
    exact ratLt_not_ratLe_reverse h
      (ratLe_of_RatEq_left same zx)

theorem ratApart0_of_pos {x : Rat} :
    ratLt ratZero x -> ratApart0 x := by
  exact ratPositive_num_nonzero

private theorem intApart0_of_length_pos_local {x : RatInt} :
    0 < bwordLength x.magnitude -> IntNonzero x := by
  intro hpos
  change intApart0 x
  by_cases unitLength : bwordLength x.magnitude = 1
  · exact Or.inr
      ((BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.right.right.left
        x.carrier.right (unary_e1_closed unary_empty)).mpr unitLength)
  · have oneLe : 1 ≤ bwordLength x.magnitude := Nat.succ_le_of_lt hpos
    have oneLt : 1 < bwordLength x.magnitude :=
      Nat.lt_of_le_of_ne oneLe (fun same => unitLength same.symm)
    exact Or.inl
      (BEDC.Derived.PadicUp.NatUnaryStrictPrefix_of_length_lt
        (unary_e1_closed unary_empty) x.carrier.right oneLt)

private theorem intMul_apart0 {x y : RatInt} :
    IntNonzero x -> IntNonzero y -> IntNonzero (IntMul x y) := by
  intro hx hy
  apply intApart0_of_length_pos_local
  have hxLen : 0 < bwordLength x.magnitude := intApart0_length_pos hx
  have hyLen : 0 < bwordLength y.magnitude := intApart0_length_pos hy
  have productLen :
      bwordLength (IntMul x y).magnitude =
        bwordLength x.magnitude * bwordLength y.magnitude :=
    BEDC.Derived.PrimeUp.NatMul_bwordLength (intMul_magnitude_natMul x y)
  rw [productLen]
  exact Nat.mul_pos hxLen hyLen

theorem ratMul_apart0 {x y : Rat} :
    ratApart0 x -> ratApart0 y -> ratApart0 (ratMul x y) := by
  intro hx hy
  unfold ratApart0 ratMul
  exact intMul_apart0 hx hy

private theorem ratNum_zero_to_RatEq_zero_local {x : Rat} :
    IntEq x.num intZero -> RatEq x ratZero := by
  intro numZero
  unfold RatEq
  change
    IntEq (IntMul x.num (ratDenInt ratZero))
      (IntMul ratZero.num (ratDenInt x))
  have leftToZero :
      IntEq (IntMul x.num (ratDenInt ratZero)) intZero :=
    IntEq_trans (intMul_left_congr (c := x.num) ratDenInt_zero)
      (IntEq_trans (intMul_one_right x.num) numZero)
  have rightToZero :
      IntEq (IntMul ratZero.num (ratDenInt x)) intZero := by
    change IntEq (IntMul intZero (ratDenInt x)) intZero
    exact intMul_zero_left (ratDenInt x)
  exact IntEq_trans leftToZero (IntEq_symm rightToZero)

theorem ratMul_nonneg {x y : Rat} :
    ratLe ratZero x -> ratLe ratZero y -> ratLe ratZero (ratMul x y) := by
  intro hx hy
  have raw : ratLe (ratMul ratZero y) (ratMul x y) :=
    ratMul_le_mul_right hx hy
  have zeroMul : RatEq (ratMul ratZero y) ratZero := by
    apply ratNum_zero_to_RatEq_zero_local
    unfold ratMul ratZero intToRat
    change IntEq (IntMul intZero y.num) intZero
    exact intMul_zero_left y.num
  exact ratLe_of_RatEq_left (RatEq_symm zeroMul) raw

theorem ratMul_le_mul_nonneg_left {a b c : Rat} :
    ratLe a b -> ratLe ratZero c -> ratLe (ratMul c a) (ratMul c b) := by
  intro h hc
  exact ratMul_le_mul_left h hc

theorem ratAdd_le_add {a b c d : Rat} :
    ratLe a b -> ratLe c d -> ratLe (ratAdd a c) (ratAdd b d) := by
  intro ab cd
  exact BEDC.Derived.LocatedReal.ratLe_add_mono ab cd

theorem ratSum_le_sum {K : Nat} {f g : Nat -> Rat} :
    (∀ j : Nat, j < K -> ratLe (f j) (g j)) ->
      ratLe (ratSum K f) (ratSum K g) := by
  induction K with
  | zero =>
      intro _h
      change ratLe ratZero ratZero
      exact ratLe_refl ratZero
  | succ K ih =>
      intro h
      change
        ratLe (ratAdd (ratSum K f) (f K))
          (ratAdd (ratSum K g) (g K))
      apply ratAdd_le_add
      · apply ih
        intro j hj
        exact h j (Nat.lt_trans hj (Nat.lt_succ_self K))
      · exact h K (Nat.lt_succ_self K)

theorem sq_lt_one_of_nonneg_lt_one {z : Rat} :
    ratLe ratZero z -> ratLt z ratOne -> ratLt (ratMul z z) ratOne := by
  intro hz0 hz1
  have raw : ratLt (ratMul z z) (ratMul ratOne ratOne) :=
    rat_sq_strictMono hz0 hz1
  exact ratLt_of_RatEq_right raw (ratOne_mul_left ratOne)

theorem one_sub_sq_apart
    (z : Rat)
    (hz0 : ratLe ratZero z)
    (hz1 : ratLt z ratOne) :
    ratApart0 (ratSub ratOne (ratMul z z)) := by
  exact ratApart0_of_pos (sub_pos_of_lt (sq_lt_one_of_nonneg_lt_one hz0 hz1))

private theorem natOne_strict_of_tail (tail : BHist) :
    UnaryHistory tail -> (tail = BHist.Empty -> False) ->
      NatUnaryStrictPrefix NatOne (BHist.e1 tail) := by
  intro tailUnary tailNonempty
  have shifted : append NatOne tail = BHist.e1 tail :=
    (unary_append_e1_left (h := tail) (k := BHist.Empty) tailUnary).trans
      (congrArg BHist.e1 (append_empty_left tail))
  exact ⟨tail, tailUnary, tailNonempty, cont_intro shifted.symm⟩

private theorem natOne_strict_natToUnary_succ_succ (n : Nat) :
    NatUnaryStrictPrefix NatOne (natToUnary (Nat.succ (Nat.succ n))) := by
  change NatUnaryStrictPrefix NatOne (BHist.e1 (natToUnary (Nat.succ n)))
  exact natOne_strict_of_tail (natToUnary (Nat.succ n))
    (natToUnary_unary (Nat.succ n)) (fun empty => by
      change BHist.e1 (natToUnary n) = BHist.Empty at empty
      exact not_hsame_e1_empty empty)

theorem oddDen_apart (M : Nat) :
    ratApart0 (oddDen M) := by
  unfold oddDen ratNat ratApart0 intToRat intOfNat
  cases M with
  | zero =>
      exact Or.inr (hsame_refl NatOne)
  | succ M =>
      apply Or.inl
      apply NatUnaryStrictPrefix_of_length_lt
      · exact unary_e1_closed unary_empty
      · exact natToUnary_unary (2 * Nat.succ M + 1)
      · rw [NatUp_unary_standard_bridge.right.left BHist.Empty unary_empty]
        rw [natToUnary_length]
        apply Nat.succ_lt_succ
        rw [NatUp_unary_standard_bridge.left]
        exact Nat.mul_pos (Nat.succ_pos 1) (Nat.succ_pos M)

theorem oddDen_pos (M : Nat) :
    ratLt ratZero (oddDen M) := by
  apply ratLe_not_le_to_ratLt
  · unfold oddDen
    exact ratNat_nonneg (2 * M + 1)
  · intro reverse
    have zeroLe : ratLe ratZero (oddDen M) := by
      unfold oddDen
      exact ratNat_nonneg (2 * M + 1)
    have same : RatEq (oddDen M) ratZero :=
      ratLe_antisymm reverse zeroLe
    exact intApart0_not_zero_pair (oddDen_apart M) (RatEq_zero_num same)

private theorem two_mul_add_one_le (M j : Nat) :
    2 * M + 1 ≤ 2 * (M + j) + 1 := by
  apply Nat.succ_le_succ
  have hM : M ≤ M + j := Nat.le_add_right M j
  exact Nat.mul_le_mul_left 2 hM

theorem oddDen_le_add (M j : Nat) :
    ratLe (oddDen M) (oddDen (M + j)) := by
  unfold oddDen
  exact ratNat_le_of_nat_le (two_mul_add_one_le M j)

theorem ratDivApart_mul_cancel_right {a b : Rat}
    (hb : ratApart0 b) :
    RatEq (ratMul (ratDivApart a b hb) b) a := by
  unfold ratDivApart
  have invMul :
      RatEq (ratMul (ratInvApart b hb) b) ratOne :=
    RatEq_trans _ _ _
      (ratMul_comm (ratInvApart b hb) b)
      (ratInvApart_mul b hb)
  exact RatEq_trans _ _ _
    (ratMul_assoc a (ratInvApart b hb) b)
    (RatEq_trans _ _ _
      (ratMul_respects (RatEq_refl a) invMul)
      (ratMul_one_right a))

private theorem ratInvApart_mul_left (x : Rat) (hx : ratApart0 x) :
    RatEq (ratMul (ratInvApart x hx) x) ratOne :=
  RatEq_trans _ _ _
    (ratMul_comm (ratInvApart x hx) x)
    (ratInvApart_mul x hx)

private theorem ratRightInverse_unique {u v c : Rat} :
    RatEq (ratMul u c) ratOne ->
      RatEq (ratMul v c) ratOne ->
        RatEq u v := by
  intro hu hv
  have cvOne : RatEq (ratMul c v) ratOne :=
    RatEq_trans _ _ _ (ratMul_comm c v) hv
  exact RatEq_trans _ _ _
    (RatEq_symm (ratMul_one_right u))
    (RatEq_trans _ _ _
      (ratMul_respects (RatEq_refl u) (RatEq_symm cvOne))
      (RatEq_trans _ _ _
        (RatEq_symm (ratMul_assoc u c v))
        (RatEq_trans _ _ _
          (ratMul_respects hu (RatEq_refl v))
          (ratOne_mul_left v))))

private theorem ratMul_inv_product_right {d g : Rat}
    (hd : ratApart0 d) (hg : ratApart0 g) :
    RatEq
      (ratMul
        (ratMul (ratInvApart d hd) (ratInvApart g hg))
        (ratMul d g))
      ratOne := by
  let invD := ratInvApart d hd
  let invG := ratInvApart g hg
  have invDLeft : RatEq (ratMul invD d) ratOne :=
    ratInvApart_mul_left d hd
  have invGLeft : RatEq (ratMul invG g) ratOne :=
    ratInvApart_mul_left g hg
  have inner :
      RatEq (ratMul invG (ratMul d g))
        (ratMul d (ratMul invG g)) :=
    RatEq_trans _ _ _
      (RatEq_symm (ratMul_assoc invG d g))
      (RatEq_trans _ _ _
        (ratMul_respects (ratMul_comm invG d) (RatEq_refl g))
        (ratMul_assoc d invG g))
  exact RatEq_trans _ _ _
    (ratMul_assoc invD invG (ratMul d g))
    (RatEq_trans _ _ _
      (ratMul_respects (RatEq_refl invD) inner)
      (RatEq_trans _ _ _
        (RatEq_symm (ratMul_assoc invD d (ratMul invG g)))
        (RatEq_trans _ _ _
          (ratMul_respects invDLeft invGLeft)
          (ratOne_mul_left ratOne))))

theorem ratInvApart_mul_product {d g : Rat}
    (hd : ratApart0 d) (hg : ratApart0 g)
    (hden : ratApart0 (ratMul d g)) :
    RatEq
      (ratInvApart (ratMul d g) hden)
      (ratMul (ratInvApart d hd) (ratInvApart g hg)) := by
  apply ratRightInverse_unique (c := ratMul d g)
  · exact ratInvApart_mul_left (ratMul d g) hden
  · exact ratMul_inv_product_right hd hg

theorem ratDivApart_scaled_geom_collapse
    (A d g : Rat)
    (hd : ratApart0 d)
    (hg : ratApart0 g)
    (hden : ratApart0 (ratMul d g)) :
    RatEq
      (ratMul
        (ratDivApart A d hd)
        (ratDivApart ratOne g hg))
      (ratDivApart A (ratMul d g) hden) := by
  unfold ratDivApart
  let invD := ratInvApart d hd
  let invG := ratInvApart g hg
  let invDG := ratInvApart (ratMul d g) hden
  have invProduct : RatEq invDG (ratMul invD invG) :=
    ratInvApart_mul_product hd hg hden
  exact RatEq_trans _ _ _
    (ratMul_respects (RatEq_refl (ratMul A invD)) (ratOne_mul_left invG))
    (RatEq_trans _ _ _
      (ratMul_assoc A invD invG)
      (ratMul_respects (RatEq_refl A) (RatEq_symm invProduct)))

private theorem intStrictPos_num_of_ratPos_local {x : Rat} :
    ratLt ratZero x -> intLtUp intZero x.num := by
  intro hlt
  unfold ratLt ratZero intToRat at hlt
  change
    intLtUp (IntMul intZero (ratDenInt x))
      (IntMul x.num (ratDenInt ratZero)) at hlt
  have leftZero :
      IntEq (IntMul intZero (ratDenInt x)) intZero :=
    intMul_zero_left (ratDenInt x)
  have rightNum :
      IntEq (IntMul x.num (ratDenInt ratZero)) x.num :=
    IntEq_trans (intMul_left_congr (c := x.num) ratDenInt_zero)
      (intMul_one_right x.num)
  exact intLt_respects leftZero rightNum hlt

private theorem intStrictPos_of_nat_with_sign_local {sign : BMark} {n : BHist}
    (hn : UnaryHistory n) :
    intLtUp intZero (intOfNatWithSign sign n hn) ->
      sign = BMark.b0 := by
  intro hpos
  cases sign with
  | b0 => rfl
  | b1 =>
      unfold intLtUp intLt intZero intOfNat intToPair at hpos
      change bwordLength BHist.Empty + bwordLength n <
        bwordLength BHist.Empty + bwordLength BHist.Empty at hpos
      rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left] at hpos
      rw [Nat.zero_add, Nat.add_zero] at hpos
      exact False.elim (Nat.not_lt_zero _ hpos)

private theorem intStrictPos_sign_zero_local {x : RatInt} :
    intLtUp intZero x -> x.sign = BMark.b0 := by
  intro hpos
  cases x with
  | mk sign magnitude carrier =>
      change intLtUp intZero
        (intOfNatWithSign sign magnitude carrier.right) at hpos
      exact intStrictPos_of_nat_with_sign_local (sign := sign)
        (n := magnitude) carrier.right hpos

private theorem ratInvApart_nonneg_of_pos_local {y : Rat}
    (hyPos : ratLt ratZero y) (hyApart : ratApart0 y) :
    ratLe ratZero (ratInvApart y hyApart) := by
  apply ratNonneg_of_num
  cases y with
  | mk num den den_pos =>
      have posNum : intLtUp intZero num :=
        intStrictPos_num_of_ratPos_local (x := RatNum.mk num den den_pos) hyPos
      have signZero : num.sign = BMark.b0 :=
        intStrictPos_sign_zero_local posNum
      change intLe intZero
        (intOfNatWithSign num.sign den
          (ratDenCarrier (RatNum.mk num den den_pos)))
      rw [signZero]
      exact intLe_zero_of_nat den
        (ratDenCarrier (RatNum.mk num den den_pos))

theorem ratDivApart_nonneg_of_nonneg_pos {a b : Rat}
    (ha : ratLe ratZero a) (hb : ratLt ratZero b) (hbApart : ratApart0 b) :
    ratLe ratZero (ratDivApart a b hbApart) := by
  unfold ratDivApart
  exact ratMul_nonneg ha (ratInvApart_nonneg_of_pos_local hb hbApart)

theorem ratPow_nonneg {z : Rat} :
    ratLe ratZero z -> ∀ n : Nat, ratLe ratZero (ratPow z n)
  | _hz0, 0 => by
      change ratLe ratZero ratOne
      apply ratNonneg_of_num
      unfold ratOne intToRat intOne intOfNat
      exact intLe_zero_of_nat NatOne (unary_e1_closed unary_empty)
  | hz0, Nat.succ n => ratMul_nonneg (ratPow_nonneg hz0 n) hz0

def oddTerm (z : Rat) (M : Nat) : Rat :=
  ratDivApart (ratPow z (2 * M + 1)) (oddDen M) (oddDen_apart M)

theorem oddTerm_nonneg {z : Rat} (hz0 : ratLe ratZero z) (M : Nat) :
    ratLe ratZero (oddTerm z M) := by
  unfold oddTerm
  exact ratDivApart_nonneg_of_nonneg_pos
    (ratPow_nonneg hz0 (2 * M + 1))
    (oddDen_pos M)
    (oddDen_apart M)

def oddTail (z : Rat) (M K : Nat) : Rat :=
  ratSum K (fun j => oddTerm z (M + j))

theorem oddTailDen_apart
    (z : Rat)
    (hz0 : ratLe ratZero z)
    (hz1 : ratLt z ratOne)
    (M : Nat) :
    ratApart0
      (ratMul
        (oddDen M)
        (ratSub ratOne (ratMul z z))) := by
  exact ratMul_apart0
    (oddDen_apart M)
    (one_sub_sq_apart z hz0 hz1)

def oddTailBound
    (z : Rat)
    (hz0 : ratLe ratZero z)
    (hz1 : ratLt z ratOne)
    (M : Nat) : Rat :=
  ratDivApart
    (ratPow z (2 * M + 1))
    (ratMul
      (oddDen M)
      (ratSub ratOne (ratMul z z)))
    (oddTailDen_apart z hz0 hz1 M)

def atanhTail (z : Rat) (M K : Nat) : Rat :=
  oddTail z M K

def atanhTailBound
    (z : Rat)
    (hz0 : ratLe ratZero z)
    (hz1 : ratLt z ratOne)
    (M : Nat) : Rat :=
  oddTailBound z hz0 hz1 M

end BEDC.Real.RatNumKernel
