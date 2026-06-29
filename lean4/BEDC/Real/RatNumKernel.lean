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

private def intProd7 (a b c d e f g : RatInt) : RatInt :=
  IntMul a (IntMul b (IntMul c (IntMul d (IntMul e (IntMul f g)))))

private theorem intMul_swap_right_assoc (a b t : RatInt) :
    IntEq (IntMul a (IntMul b t)) (IntMul b (IntMul a t)) := by
  let R := BEDC.Algebra.Rel.IntegerUp_RelCommRing
  exact R.trans (R.symm (R.mul_assoc a b t))
    (R.trans (R.mul_congr (R.mul_comm a b) (R.refl t))
      (R.mul_assoc b a t))

private theorem intProd7_swap_3_4 (a b c d e f g : RatInt) :
    IntEq (intProd7 a b c d e f g) (intProd7 a b d c e f g) := by
  unfold intProd7
  exact intMul_left_congr (c := a)
    (intMul_left_congr (c := b)
      (intMul_swap_right_assoc c d (IntMul e (IntMul f g))))

private theorem intProd7_swap_5_6 (a b c d e f g : RatInt) :
    IntEq (intProd7 a b c d e f g) (intProd7 a b c d f e g) := by
  unfold intProd7
  exact intMul_left_congr (c := a)
    (intMul_left_congr (c := b)
      (intMul_left_congr (c := c)
        (intMul_left_congr (c := d)
          (intMul_swap_right_assoc e f g))))

private theorem intProd7_tail_perm (a b y p q r : RatInt) :
    IntEq (intProd7 a b y p q p r) (intProd7 a b p y p q r) := by
  exact IntEq_trans (intProd7_swap_3_4 a b y p q p r)
    (intProd7_swap_5_6 a b p y q p r)

private theorem intMul_left_expanded_term_to_prod7
    (an x y ad bd cd : RatInt) :
    IntEq
      (IntMul (IntMul an (IntMul x y))
        (IntMul (IntMul ad bd) (IntMul ad cd)))
      (intProd7 an x y ad bd ad cd) := by
  let dLeft := IntMul (IntMul ad bd) (IntMul ad cd)
  have h1 :
      IntEq
        (IntMul (IntMul an (IntMul x y)) dLeft)
        (IntMul an (IntMul (IntMul x y) dLeft)) :=
    intMul_assoc an (IntMul x y) dLeft
  have h2 :
      IntEq (IntMul (IntMul x y) dLeft)
        (IntMul x (IntMul y dLeft)) :=
    intMul_assoc x y dLeft
  have hD :
      IntEq dLeft (IntMul ad (IntMul bd (IntMul ad cd))) :=
    intMul_assoc ad bd (IntMul ad cd)
  have h3 :
      IntEq (IntMul an (IntMul (IntMul x y) dLeft))
        (intProd7 an x y ad bd ad cd) := by
    unfold intProd7
    exact intMul_left_congr (c := an)
      (IntEq_trans h2
        (intMul_left_congr (c := x)
          (intMul_left_congr (c := y) hD)))
  exact IntEq_trans h1 h3

private theorem intMul_right_expanded_term_to_prod7
    (an x y ad bd cd : RatInt) :
    IntEq
      (IntMul (IntMul (IntMul an x) (IntMul ad y))
        (IntMul ad (IntMul bd cd)))
      (intProd7 an x ad y ad bd cd) := by
  let dRight := IntMul ad (IntMul bd cd)
  have h1 :
      IntEq
        (IntMul (IntMul (IntMul an x) (IntMul ad y)) dRight)
        (IntMul (IntMul an x) (IntMul (IntMul ad y) dRight)) :=
    intMul_assoc (IntMul an x) (IntMul ad y) dRight
  have h2 :
      IntEq (IntMul (IntMul an x) (IntMul (IntMul ad y) dRight))
        (IntMul an (IntMul x (IntMul (IntMul ad y) dRight))) :=
    intMul_assoc an x (IntMul (IntMul ad y) dRight)
  have h3 :
      IntEq (IntMul (IntMul ad y) dRight)
        (IntMul ad (IntMul y dRight)) :=
    intMul_assoc ad y dRight
  have h4 :
      IntEq (IntMul an (IntMul x (IntMul (IntMul ad y) dRight)))
        (intProd7 an x ad y ad bd cd) := by
    unfold intProd7
    exact intMul_left_congr (c := an)
      (intMul_left_congr (c := x) h3)
  exact IntEq_trans h1 (IntEq_trans h2 h4)

theorem ratMul_add_left (a b c : Rat) :
    RatEq (ratMul a (ratAdd b c))
      (ratAdd (ratMul a b) (ratMul a c)) := by
  unfold RatEq
  change IntEq
    (IntMul (IntMul a.num (ratAdd b c).num)
      (ratDenInt (ratAdd (ratMul a b) (ratMul a c))))
    (IntMul (ratAdd (ratMul a b) (ratMul a c)).num
      (ratDenInt (ratMul a (ratAdd b c))))
  let ad := ratDenInt a
  let bd := ratDenInt b
  let cd := ratDenInt c
  let bn := b.num
  let cn := c.num
  let an := a.num
  have hAddNum : IntEq (ratAdd b c).num (IntAdd (IntMul bn cd) (IntMul cn bd)) := by
    unfold bn cn bd cd ratAdd ratDenInt
    exact IntEq_refl _
  have hDenLeft :
      IntEq (ratDenInt (ratAdd (ratMul a b) (ratMul a c)))
        (IntMul (IntMul ad bd) (IntMul ad cd)) := by
    exact IntEq_trans (ratDenInt_add (ratMul a b) (ratMul a c))
      (BEDC.Derived.RationalUp.IntMul_respects
        (ratDenInt_mul a b) (ratDenInt_mul a c))
  have hDenRight :
      IntEq (ratDenInt (ratMul a (ratAdd b c)))
        (IntMul ad (IntMul bd cd)) := by
    exact IntEq_trans (ratDenInt_mul a (ratAdd b c))
      (BEDC.Derived.RationalUp.IntMul_respects
        (IntEq_refl ad) (ratDenInt_add b c))
  have hNumRight :
      IntEq (ratAdd (ratMul a b) (ratMul a c)).num
        (IntAdd
          (IntMul (IntMul an bn) (IntMul ad cd))
          (IntMul (IntMul an cn) (IntMul ad bd))) := by
    unfold an bn cn ad bd cd
    change IntEq
      (IntAdd
        (IntMul (IntMul a.num b.num) (ratDenInt (ratMul a c)))
        (IntMul (IntMul a.num c.num) (ratDenInt (ratMul a b))))
      (IntAdd
        (IntMul (IntMul a.num b.num) (IntMul (ratDenInt a) (ratDenInt c)))
        (IntMul (IntMul a.num c.num) (IntMul (ratDenInt a) (ratDenInt b))))
    exact BEDC.Derived.RationalUp.IntAdd_respects
      (BEDC.Derived.RationalUp.IntMul_respects (IntEq_refl _) (ratDenInt_mul a c))
      (BEDC.Derived.RationalUp.IntMul_respects (IntEq_refl _) (ratDenInt_mul a b))
  have leftStructured :
      IntEq
        (IntMul (IntMul an (ratAdd b c).num)
          (ratDenInt (ratAdd (ratMul a b) (ratMul a c))))
        (IntMul (IntMul an (IntAdd (IntMul bn cd) (IntMul cn bd)))
          (IntMul (IntMul ad bd) (IntMul ad cd))) := by
    exact BEDC.Derived.RationalUp.IntMul_respects
      (BEDC.Derived.RationalUp.IntMul_respects (IntEq_refl an) hAddNum)
      hDenLeft
  have rightStructured :
      IntEq
        (IntMul (ratAdd (ratMul a b) (ratMul a c)).num
          (ratDenInt (ratMul a (ratAdd b c))))
        (IntMul
          (IntAdd
            (IntMul (IntMul an bn) (IntMul ad cd))
            (IntMul (IntMul an cn) (IntMul ad bd)))
          (IntMul ad (IntMul bd cd))) := by
    exact BEDC.Derived.RationalUp.IntMul_respects hNumRight hDenRight
  have core :
      IntEq
        (IntMul (IntMul an (IntAdd (IntMul bn cd) (IntMul cn bd)))
          (IntMul (IntMul ad bd) (IntMul ad cd)))
        (IntMul
          (IntAdd
            (IntMul (IntMul an bn) (IntMul ad cd))
            (IntMul (IntMul an cn) (IntMul ad bd)))
          (IntMul ad (IntMul bd cd))) := by
    let R := BEDC.Algebra.Rel.IntegerUp_RelCommRing
    let dLeft := IntMul (IntMul ad bd) (IntMul ad cd)
    let dRight := IntMul ad (IntMul bd cd)
    have expandLeftA :
        IntEq (IntMul an (IntAdd (IntMul bn cd) (IntMul cn bd)))
          (IntAdd (IntMul an (IntMul bn cd)) (IntMul an (IntMul cn bd))) :=
      R.left_distrib an (IntMul bn cd) (IntMul cn bd)
    have expandLeft :
        IntEq
          (IntMul (IntMul an (IntAdd (IntMul bn cd) (IntMul cn bd))) dLeft)
          (IntAdd
            (IntMul (IntMul an (IntMul bn cd)) dLeft)
            (IntMul (IntMul an (IntMul cn bd)) dLeft)) :=
      IntEq_trans
        (BEDC.Derived.RationalUp.IntMul_respects expandLeftA (IntEq_refl dLeft))
        (R.right_distrib (IntMul an (IntMul bn cd)) (IntMul an (IntMul cn bd)) dLeft)
    have expandRight :
        IntEq
          (IntMul
            (IntAdd
              (IntMul (IntMul an bn) (IntMul ad cd))
              (IntMul (IntMul an cn) (IntMul ad bd))) dRight)
          (IntAdd
            (IntMul (IntMul (IntMul an bn) (IntMul ad cd)) dRight)
            (IntMul (IntMul (IntMul an cn) (IntMul ad bd)) dRight)) :=
      R.right_distrib
        (IntMul (IntMul an bn) (IntMul ad cd))
        (IntMul (IntMul an cn) (IntMul ad bd)) dRight
    have term1 :
        IntEq
          (IntMul (IntMul an (IntMul bn cd)) dLeft)
          (IntMul (IntMul (IntMul an bn) (IntMul ad cd)) dRight) := by
      exact IntEq_trans (intMul_left_expanded_term_to_prod7 an bn cd ad bd cd)
        (IntEq_trans (intProd7_tail_perm an bn cd ad bd cd)
          (IntEq_symm (intMul_right_expanded_term_to_prod7 an bn cd ad bd cd)))
    have term2 :
        IntEq
          (IntMul (IntMul an (IntMul cn bd)) dLeft)
          (IntMul (IntMul (IntMul an cn) (IntMul ad bd)) dRight) := by
      exact IntEq_trans (intMul_left_expanded_term_to_prod7 an cn bd ad bd cd)
        (IntEq_trans (intProd7_tail_perm an cn bd ad bd cd)
          (IntEq_symm (intMul_right_expanded_term_to_prod7 an cn bd ad bd cd)))
    exact IntEq_trans expandLeft
      (IntEq_trans (BEDC.Derived.RationalUp.IntAdd_respects term1 term2)
        (IntEq_symm expandRight))
  exact IntEq_trans leftStructured
    (IntEq_trans core (IntEq_symm rightStructured))

theorem ratMul_add_right (a b c : Rat) :
    RatEq (ratMul (ratAdd a b) c)
      (ratAdd (ratMul a c) (ratMul b c)) := by
  exact RatEq_trans _ _ _
    (ratMul_comm (ratAdd a b) c)
    (RatEq_trans _ _ _
      (ratMul_add_left c a b)
      (ratAdd_respects (ratMul_comm c a) (ratMul_comm c b)))

private theorem ratMul_zero_left_local (x : Rat) :
    RatEq (ratMul ratZero x) ratZero := by
  apply ratNum_zero_to_RatEq_zero_local
  unfold ratMul ratZero intToRat
  change IntEq (IntMul intZero x.num) intZero
  exact intMul_zero_left x.num

private theorem ratMul_zero_right_local (x : Rat) :
    RatEq (ratMul x ratZero) ratZero := by
  exact RatEq_trans _ _ _
    (ratMul_comm x ratZero)
    (ratMul_zero_left_local x)

private theorem ratSub_add_cancel_right_local (x y : Rat) :
    RatEq (ratAdd (ratSub x y) y) x := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (BEDC.Derived.LocatedReal.ratAdd_assoc_local x (ratNeg y) y)
    (RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl x) (BEDC.Derived.LocatedReal.ratNeg_add_local y))
      (ratAdd_zero_right x))

private theorem ratMul_neg_right_local (x y : Rat) :
    RatEq (ratMul x (ratNeg y)) (ratNeg (ratMul x y)) := by
  apply ratEq_of_num_den_intEq
  · unfold ratMul ratNeg
    exact BEDC.Algebra.Rel.IntegerUp_mul_neg x.num y.num
  · unfold ratMul ratNeg ratDenInt
    exact IntEq_refl _

private theorem gap_mul_add_cancel (q p : Rat) :
    RatEq (ratAdd (ratMul (ratSub ratOne q) p) (ratMul p q)) p := by
  have commuteGap :
      RatEq (ratMul (ratSub ratOne q) p)
        (ratMul p (ratSub ratOne q)) :=
    ratMul_comm (ratSub ratOne q) p
  have expandGap :
      RatEq (ratMul p (ratSub ratOne q))
        (ratSub p (ratMul p q)) := by
    unfold ratSub
    have dist :
        RatEq (ratMul p (ratAdd ratOne (ratNeg q)))
          (ratAdd (ratMul p ratOne) (ratMul p (ratNeg q))) :=
      ratMul_add_left p ratOne (ratNeg q)
    exact RatEq_trans _ _ _ dist
      (ratAdd_respects (ratMul_one_right p) (ratMul_neg_right_local p q))
  exact RatEq_trans _ _ _
    (ratAdd_respects
      (RatEq_trans _ _ _ commuteGap expandGap)
      (RatEq_refl (ratMul p q)))
    (ratSub_add_cancel_right_local p (ratMul p q))

theorem ratPow_add (x : Rat) (m n : Nat) :
    RatEq (ratPow x (m + n)) (ratMul (ratPow x m) (ratPow x n)) := by
  induction n with
  | zero =>
      rw [Nat.add_zero]
      change RatEq (ratPow x m) (ratMul (ratPow x m) ratOne)
      exact RatEq_symm (ratMul_one_right (ratPow x m))
  | succ n ih =>
      rw [Nat.add_succ]
      change RatEq (ratMul (ratPow x (m + n)) x)
        (ratMul (ratPow x m) (ratMul (ratPow x n) x))
      exact RatEq_trans _ _ _
        (ratMul_respects ih (RatEq_refl x))
        (ratMul_assoc (ratPow x m) (ratPow x n) x)

private theorem ratPow_two (z : Rat) :
    RatEq (ratPow z 2) (ratMul z z) := by
  change RatEq (ratMul (ratMul ratOne z) z) (ratMul z z)
  exact ratMul_respects (ratOne_mul_left z) (RatEq_refl z)

theorem ratPow_sq_base (z : Rat) (j : Nat) :
    RatEq (ratPow z (2 * j)) (ratPow (ratMul z z) j) := by
  induction j with
  | zero =>
      change RatEq ratOne ratOne
      exact RatEq_refl ratOne
  | succ j ih =>
      rw [Nat.mul_succ]
      change RatEq (ratPow z (2 * j + 2))
        (ratMul (ratPow (ratMul z z) j) (ratMul z z))
      have split :
          RatEq (ratPow z (2 * j + 2))
            (ratMul (ratPow z (2 * j)) (ratPow z 2)) :=
        ratPow_add z (2 * j) 2
      exact RatEq_trans _ _ _ split
        (ratMul_respects ih (ratPow_two z))

private theorem odd_index_split_nat (M j : Nat) :
    2 * (M + j) + 1 = 2 * M + 1 + 2 * j := by
  calc
    2 * (M + j) + 1 = (2 * M + 2 * j) + 1 := by
      rw [Nat.mul_add]
    _ = 2 * M + (2 * j + 1) := Nat.add_assoc (2 * M) (2 * j) 1
    _ = 2 * M + (1 + 2 * j) :=
      congrArg (fun t => 2 * M + t) (Nat.add_comm (2 * j) 1)
    _ = 2 * M + 1 + 2 * j := (Nat.add_assoc (2 * M) 1 (2 * j)).symm

theorem oddPow_split (z : Rat) (M j : Nat) :
    RatEq (ratPow z (2 * (M + j) + 1))
      (ratMul (ratPow z (2 * M + 1)) (ratPow (ratMul z z) j)) := by
  rw [odd_index_split_nat M j]
  exact RatEq_trans _ _ _
    (ratPow_add z (2 * M + 1) (2 * j))
    (ratMul_respects (RatEq_refl (ratPow z (2 * M + 1)))
      (ratPow_sq_base z j))

theorem ratMul_sum_left (a : Rat) (K : Nat) (f : Nat -> Rat) :
    RatEq (ratMul a (ratSum K f)) (ratSum K (fun j => ratMul a (f j))) := by
  induction K with
  | zero =>
      change RatEq (ratMul a ratZero) ratZero
      exact ratMul_zero_right_local a
  | succ K ih =>
      change RatEq (ratMul a (ratAdd (ratSum K f) (f K)))
        (ratAdd (ratSum K (fun j => ratMul a (f j))) (ratMul a (f K)))
      exact RatEq_trans _ _ _
        (ratMul_add_left a (ratSum K f) (f K))
        (ratAdd_respects ih (RatEq_refl (ratMul a (f K))))

private theorem geom_telescopes (q : Rat) (K : Nat) :
    RatEq
      (ratAdd (ratMul (ratSub ratOne q) (geomSum q K)) (ratPow q K))
      ratOne := by
  induction K with
  | zero =>
      change RatEq (ratAdd (ratMul (ratSub ratOne q) ratZero) ratOne) ratOne
      exact RatEq_trans _ _ _
        (ratAdd_respects (ratMul_zero_right_local (ratSub ratOne q)) (RatEq_refl ratOne))
        (ratZero_add_left ratOne)
  | succ K ih =>
      change RatEq
        (ratAdd
          (ratMul (ratSub ratOne q)
            (ratAdd (geomSum q K) (ratPow q K)))
          (ratMul (ratPow q K) q)) ratOne
      let gap := ratSub ratOne q
      let s := geomSum q K
      let p := ratPow q K
      have distribute :
          RatEq (ratMul gap (ratAdd s p))
            (ratAdd (ratMul gap s) (ratMul gap p)) :=
        ratMul_add_left gap s p
      have regroup :
          RatEq
            (ratAdd (ratAdd (ratMul gap s) (ratMul gap p)) (ratMul p q))
            (ratAdd (ratMul gap s) (ratAdd (ratMul gap p) (ratMul p q))) :=
        BEDC.Derived.LocatedReal.ratAdd_assoc_local
          (ratMul gap s) (ratMul gap p) (ratMul p q)
      have inner :
          RatEq (ratAdd (ratMul gap p) (ratMul p q)) p := by
        unfold gap
        exact gap_mul_add_cancel q p
      have toPrevious :
          RatEq
            (ratAdd
              (ratMul (ratSub ratOne q)
                (ratAdd (geomSum q K) (ratPow q K)))
              (ratMul (ratPow q K) q))
            (ratAdd (ratMul gap s) p) := by
        exact RatEq_trans _ _ _
          (ratAdd_respects distribute (RatEq_refl (ratMul p q)))
          (RatEq_trans _ _ _
            regroup
            (ratAdd_respects (RatEq_refl (ratMul gap s)) inner))
      exact RatEq_trans _ _ _ toPrevious ih

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

theorem geomSum_le_inv_one_sub
    (q : Rat)
    (hq0 : ratLe ratZero q)
    (hq1 : ratLt q ratOne)
    (K : Nat)
    (hgap : ratApart0 (ratSub ratOne q)) :
    ratLe (geomSum q K)
      (ratDivApart ratOne (ratSub ratOne q) hgap) := by
  let gap := ratSub ratOne q
  let s := geomSum q K
  let p := ratPow q K
  have telescopes :
      RatEq (ratAdd (ratMul gap s) p) ratOne := by
    unfold gap s p
    exact geom_telescopes q K
  have pNonneg : ratLe ratZero p := by
    unfold p
    exact ratPow_nonneg hq0 K
  have gapTimesSumLeWithTail :
      ratLe (ratMul gap s) (ratAdd (ratMul gap s) p) := by
    have shifted :
        ratLe (ratAdd (ratMul gap s) ratZero)
          (ratAdd (ratMul gap s) p) :=
      BEDC.Derived.LocatedReal.ratLe_add_left_mono
        (x := ratMul gap s) pNonneg
    exact ratLe_of_RatEq_left
      (RatEq_symm (ratAdd_zero_right (ratMul gap s)))
      shifted
  have gapTimesSumLeOne : ratLe (ratMul gap s) ratOne :=
    ratLe_of_RatEq_right gapTimesSumLeWithTail telescopes
  have gapPos : ratLt ratZero gap := by
    unfold gap
    exact sub_pos_of_lt hq1
  have multipliedTarget :
      RatEq
        (ratMul (ratDivApart ratOne gap hgap) gap)
        ratOne :=
    ratDivApart_mul_cancel_right hgap
  have productLe :
      ratLe (ratMul s gap)
        (ratMul (ratDivApart ratOne gap hgap) gap) := by
    exact ratLe_of_RatEq_right
      (ratLe_of_RatEq_left (ratMul_comm s gap) gapTimesSumLeOne)
      (RatEq_symm multipliedTarget)
  exact ratMul_le_cancel_right gapPos productLe

private theorem ratDivApart_antitone_den_pos {x a b : Rat}
    (hx : ratLe ratZero x)
    (ha : ratLt ratZero a)
    (hb : ratLt ratZero b)
    (haApart : ratApart0 a)
    (hbApart : ratApart0 b)
    (hab : ratLe a b) :
    ratLe (ratDivApart x b hbApart) (ratDivApart x a haApart) := by
  have leftCancel :
      RatEq (ratMul (ratDivApart x b hbApart) b) x :=
    ratDivApart_mul_cancel_right hbApart
  have rightCancel :
      RatEq (ratMul (ratDivApart x a haApart) a) x :=
    ratDivApart_mul_cancel_right haApart
  have divBNonneg :
      ratLe ratZero (ratDivApart x b hbApart) :=
    ratDivApart_nonneg_of_nonneg_pos hx hb hbApart
  have step :
      ratLe (ratMul (ratDivApart x b hbApart) a)
        (ratMul (ratDivApart x b hbApart) b) := by
    exact ratMul_le_mul_nonneg_left hab divBNonneg
  have toX :
      ratLe (ratMul (ratDivApart x b hbApart) a) x :=
    ratLe_of_RatEq_right step leftCancel
  have targetMul :
      ratLe (ratMul (ratDivApart x b hbApart) a)
        (ratMul (ratDivApart x a haApart) a) :=
    ratLe_of_RatEq_right toX (RatEq_symm rightCancel)
  exact ratMul_le_cancel_right ha targetMul

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

private theorem oddTerm_le_scaled_geom_term
    (z : Rat)
    (hz0 : ratLe ratZero z)
    (M j : Nat) :
    ratLe (oddTerm z (M + j))
      (ratMul
        (ratDivApart (ratPow z (2 * M + 1)) (oddDen M) (oddDen_apart M))
        (ratPow (ratMul z z) j)) := by
  unfold oddTerm
  let x := ratPow z (2 * (M + j) + 1)
  let y := ratMul (ratPow z (2 * M + 1)) (ratPow (ratMul z z) j)
  have xy : RatEq x y := by
    unfold x y
    exact oddPow_split z M j
  have yNonneg : ratLe ratZero y := by
    unfold y
    exact ratMul_nonneg
      (ratPow_nonneg hz0 (2 * M + 1))
      (ratPow_nonneg (ratMul_nonneg hz0 hz0) j)
  have divLe :
      ratLe
        (ratDivApart y (oddDen (M + j)) (oddDen_apart (M + j)))
        (ratDivApart y (oddDen M) (oddDen_apart M)) := by
    exact ratDivApart_antitone_den_pos yNonneg
      (oddDen_pos M)
      (oddDen_pos (M + j))
      (oddDen_apart M)
      (oddDen_apart (M + j))
      (oddDen_le_add M j)
  have leftEq :
      RatEq
        (ratDivApart x (oddDen (M + j)) (oddDen_apart (M + j)))
        (ratDivApart y (oddDen (M + j)) (oddDen_apart (M + j))) := by
    unfold ratDivApart
    exact ratMul_respects xy (RatEq_refl _)
  have rightEq :
      RatEq
        (ratDivApart y (oddDen M) (oddDen_apart M))
        (ratMul
          (ratDivApart (ratPow z (2 * M + 1)) (oddDen M) (oddDen_apart M))
          (ratPow (ratMul z z) j)) := by
    unfold y ratDivApart
    exact RatEq_trans _ _ _
      (ratMul_assoc
        (ratPow z (2 * M + 1))
        (ratPow (ratMul z z) j)
        (ratInvApart (oddDen M) (oddDen_apart M)))
      (RatEq_trans _ _ _
        (ratMul_respects (RatEq_refl (ratPow z (2 * M + 1)))
          (ratMul_comm
            (ratPow (ratMul z z) j)
            (ratInvApart (oddDen M) (oddDen_apart M))))
        (RatEq_symm
          (ratMul_assoc
            (ratPow z (2 * M + 1))
            (ratInvApart (oddDen M) (oddDen_apart M))
            (ratPow (ratMul z z) j))))
  exact ratLe_of_RatEq_right (ratLe_of_RatEq_left leftEq divLe) rightEq

theorem oddTail_le_scaled_geom
    (z : Rat)
    (hz0 : ratLe ratZero z)
    (M K : Nat)
    (_hd : ratApart0 (oddDen M)) :
    ratLe (oddTail z M K)
      (ratMul
        (ratDivApart (ratPow z (2 * M + 1)) (oddDen M) (oddDen_apart M))
        (geomSum (ratMul z z) K)) := by
  unfold oddTail geomSum
  let scale := ratDivApart (ratPow z (2 * M + 1)) (oddDen M) (oddDen_apart M)
  let q := ratMul z z
  have termwise :
      ratLe
        (ratSum K (fun j => oddTerm z (M + j)))
        (ratSum K (fun j => ratMul scale (ratPow q j))) := by
    apply ratSum_le_sum
    intro j _hj
    unfold scale q
    exact oddTerm_le_scaled_geom_term z hz0 M j
  have sumEq :
      RatEq
        (ratSum K (fun j => ratMul scale (ratPow q j)))
        (ratMul scale (ratSum K (fun j => ratPow q j))) :=
    RatEq_symm (ratMul_sum_left scale K (fun j => ratPow q j))
  exact ratLe_of_RatEq_right termwise sumEq

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

theorem geom_odd_tail_kernel_raw
    (z : Rat)
    (hz0 : ratLe ratZero z)
    (hz1 : ratLt z ratOne)
    (M K : Nat) :
    ratLe (oddTail z M K) (oddTailBound z hz0 hz1 M) := by
  let q := ratMul z z
  let A := ratPow z (2 * M + 1)
  let d := oddDen M
  let gap := ratSub ratOne q
  let hd : ratApart0 d := oddDen_apart M
  let hgap : ratApart0 gap := one_sub_sq_apart z hz0 hz1
  let hden : ratApart0 (ratMul d gap) := oddTailDen_apart z hz0 hz1 M
  let scale := ratDivApart A d hd
  have hTailToGeom :
      ratLe (oddTail z M K)
        (ratMul scale (geomSum q K)) := by
    unfold scale q A d hd
    exact oddTail_le_scaled_geom z hz0 M K (oddDen_apart M)
  have hA_nonneg : ratLe ratZero A := by
    unfold A
    exact ratPow_nonneg hz0 (2 * M + 1)
  have hScaleNonneg : ratLe ratZero scale := by
    unfold scale A d hd
    exact ratDivApart_nonneg_of_nonneg_pos
      hA_nonneg
      (oddDen_pos M)
      (oddDen_apart M)
  have hqNonneg : ratLe ratZero q := by
    unfold q
    exact ratMul_nonneg hz0 hz0
  have hqLtOne : ratLt q ratOne := by
    unfold q
    exact sq_lt_one_of_nonneg_lt_one hz0 hz1
  have hGeom :
      ratLe (geomSum q K) (ratDivApart ratOne gap hgap) := by
    unfold gap hgap
    exact geomSum_le_inv_one_sub q hqNonneg hqLtOne K
      (one_sub_sq_apart z hz0 hz1)
  have hScaled :
      ratLe
        (ratMul scale (geomSum q K))
        (ratMul scale (ratDivApart ratOne gap hgap)) :=
    ratMul_le_mul_nonneg_left hGeom hScaleNonneg
  have hCollapse :
      RatEq
        (ratMul scale (ratDivApart ratOne gap hgap))
        (ratDivApart A (ratMul d gap) hden) := by
    unfold scale
    exact ratDivApart_scaled_geom_collapse A d gap hd hgap hden
  exact ratLe_of_RatEq_right
    (ratLe_trans hTailToGeom hScaled)
    hCollapse

theorem geom_odd_tail_kernel_raw_forall
    (z : Rat)
    (hz0 : ratLe ratZero z)
    (hz1 : ratLt z ratOne) :
    ∀ M K : Nat, ratLe (oddTail z M K) (oddTailBound z hz0 hz1 M) := by
  intro M K
  exact geom_odd_tail_kernel_raw z hz0 hz1 M K

theorem atanh_tail_kernel
    (z : Rat)
    (hz0 : ratLe ratZero z)
    (hz1 : ratLt z ratOne)
    (M K : Nat) :
    ratLe (atanhTail z M K) (atanhTailBound z hz0 hz1 M) := by
  exact geom_odd_tail_kernel_raw z hz0 hz1 M K

end BEDC.Real.RatNumKernel
