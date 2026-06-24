import BEDC.Derived.PrimeUp.FactorizationList
import BEDC.Derived.PrimeUp.UnitResult
import BEDC.Derived.PadicUp
import BEDC.Derived.IntUp.Arithmetic

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary
open BEDC.FKernel.Mark
open BEDC.Derived.NatUp
open BEDC.Derived.IntUp
open BEDC.Derived.PadicUp

private def NatFactor (d n : Nat) : Prop :=
  ∃ q : Nat, n = d * q

private theorem nat_mul_assoc_pure (a b c : Nat) : (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      calc
        (a * b) * Nat.succ c = (a * b) * c + a * b := Nat.mul_succ (a * b) c
        _ = a * (b * c) + a * b := congrArg (fun x => x + a * b) ih
        _ = a * (b * c + b) := (Nat.mul_add a (b * c) b).symm
        _ = a * (b * Nat.succ c) := congrArg (fun x => a * x) (Nat.mul_succ b c).symm

private def natFactorSearchFrom (fuel n d q0 : Nat) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
      if d * q0 = n then some q0 else natFactorSearchFrom fuel' n d (q0 + 1)

private def natFactorSearch (n d : Nat) : Option Nat :=
  natFactorSearchFrom (n + 1) n d 0

private theorem natFactorSearchFrom_sound {fuel n d q0 q : Nat} :
    natFactorSearchFrom fuel n d q0 = some q -> n = d * q := by
  intro found
  induction fuel generalizing q0 with
  | zero =>
      unfold natFactorSearchFrom at found
      cases found
  | succ fuel ih =>
      unfold natFactorSearchFrom at found
      by_cases product : d * q0 = n
      · rw [if_pos product] at found
        cases found
        exact product.symm
      · rw [if_neg product] at found
        exact ih found

private theorem natFactorSearch_sound {n d q : Nat} :
    natFactorSearch n d = some q -> n = d * q := by
  intro found
  exact natFactorSearchFrom_sound found

private theorem natFactorSearchFrom_none_no_match
    {fuel n d q0 q : Nat} :
    natFactorSearchFrom fuel n d q0 = none ->
      q0 ≤ q -> q < q0 + fuel -> d * q = n -> False := by
  induction fuel generalizing q0 q with
  | zero =>
      intro absent qLower qUpper product
      have qUpper' : q < q0 := by
        rw [Nat.add_zero] at qUpper
        exact qUpper
      have notLt : q < q0 -> False := fun qLt =>
        Nat.lt_irrefl q0 (Nat.lt_of_le_of_lt qLower qLt)
      exact notLt qUpper'
  | succ fuel ih =>
      intro absent qLower qUpper product
      unfold natFactorSearchFrom at absent
      by_cases current : d * q0 = n
      · rw [if_pos current] at absent
        cases absent
      · rw [if_neg current] at absent
        by_cases sameQ : q = q0
        · cases sameQ
          exact current product
        · have q0LtQ : q0 < q :=
            Nat.lt_of_le_of_ne qLower (fun eq => sameQ eq.symm)
          have nextLower : q0 + 1 ≤ q := Nat.succ_le_of_lt q0LtQ
          have nextUpper : q < q0 + 1 + fuel := by
            have sumEq : q0 + (fuel + 1) = q0 + 1 + fuel := by
              rw [Nat.add_assoc, Nat.add_comm fuel 1]
            exact Nat.lt_of_lt_of_eq qUpper sumEq
          exact ih absent nextLower nextUpper product

private theorem natFactorSearch_none_no_factor_bounded {n d q : Nat} :
    natFactorSearch n d = none -> q ≤ n -> n = d * q -> False := by
  intro absent qUpper product
  unfold natFactorSearch at absent
  have qLower : 0 ≤ q := Nat.zero_le q
  have qInSearch : q < 0 + (n + 1) := by
    rw [Nat.zero_add]
    exact Nat.lt_succ_of_le qUpper
  exact natFactorSearchFrom_none_no_match absent qLower qInSearch product.symm

private def minFactorNatFrom (fuel n d : Nat) : Nat :=
  match fuel with
  | 0 => n
  | fuel' + 1 =>
      if d ≤ n then
        match natFactorSearch n d with
        | some _ => d
        | none => minFactorNatFrom fuel' n (d + 1)
      else n

def minFactorNat (n : Nat) : Nat :=
  minFactorNatFrom n n 2

def minFactor (n : BHist) (_large : NatUnaryStrictPrefix NatOne n) : BHist :=
  natToUnary (minFactorNat (bwordLength n))

private theorem minFactorNatFrom_bound
    (fuel n d : Nat) (hd : 2 ≤ d) (hn : 2 ≤ n) :
    2 ≤ minFactorNatFrom fuel n d ∧ minFactorNatFrom fuel n d ≤ n := by
  induction fuel generalizing d with
  | zero =>
      unfold minFactorNatFrom
      exact ⟨hn, Nat.le_refl n⟩
  | succ fuel ih =>
      unfold minFactorNatFrom
      by_cases hdn : d ≤ n
      · rw [if_pos hdn]
        cases found : natFactorSearch n d with
        | some q =>
            exact ⟨hd, hdn⟩
        | none =>
            exact ih (d + 1) (Nat.le_trans hd (Nat.le_succ d))
      · rw [if_neg hdn]
        exact ⟨hn, Nat.le_refl n⟩

theorem minFactorNat_bound {n : Nat} :
    2 ≤ n -> 2 ≤ minFactorNat n ∧ minFactorNat n ≤ n := by
  intro hn
  exact minFactorNatFrom_bound n n 2 (Nat.le_refl 2) hn

private theorem minFactorNatFrom_factor (fuel n d : Nat) :
    NatFactor (minFactorNatFrom fuel n d) n := by
  induction fuel generalizing d with
  | zero =>
      unfold minFactorNatFrom
      exact ⟨1, (Nat.mul_one n).symm⟩
  | succ fuel ih =>
      unfold minFactorNatFrom
      by_cases hdn : d ≤ n
      · rw [if_pos hdn]
        cases found : natFactorSearch n d with
        | some q =>
            exact ⟨q, natFactorSearch_sound found⟩
        | none =>
            exact ih (d + 1)
      · rw [if_neg hdn]
        exact ⟨1, (Nat.mul_one n).symm⟩

private theorem minFactorNat_factor {n : Nat} :
    NatFactor (minFactorNat n) n := by
  unfold minFactorNat
  exact minFactorNatFrom_factor n n 2

private theorem NatFactor_factor_le_of_nonzero_product {d n : Nat} :
    2 ≤ n -> 1 ≤ d -> NatFactor d n -> d ≤ n := by
  intro hn hd factor
  cases factor with
  | intro q product =>
      cases q with
      | zero =>
          rw [Nat.mul_zero] at product
          rw [product] at hn
          exact False.elim (Nat.not_succ_le_zero 1 hn)
      | succ q =>
          rw [product]
          exact Nat.le_mul_of_pos_right d (Nat.succ_pos q)

private theorem NatFactor_witness_le_product {d n q : Nat} :
    0 < d -> n = d * q -> q ≤ n := by
  intro dPositive product
  rw [product]
  exact Nat.le_mul_of_pos_left q dPositive

private theorem NatFactor_trans {a b c : Nat} :
    NatFactor a b -> NatFactor b c -> NatFactor a c := by
  intro left right
  cases left with
  | intro q leftProduct =>
      cases right with
      | intro r rightProduct =>
          exact ⟨q * r, by
            calc
              c = b * r := rightProduct
              _ = (a * q) * r := congrArg (fun x => x * r) leftProduct
              _ = a * (q * r) := nat_mul_assoc_pure a q r⟩

private theorem minFactorNatFrom_minimal
    (fuel n d a : Nat) :
    2 ≤ n -> 2 ≤ d -> d ≤ a -> a < d + fuel -> NatFactor a n ->
      minFactorNatFrom fuel n d ≤ a := by
  intro hn hd hda halt factorAN
  induction fuel generalizing d with
  | zero =>
      have alt : a < d := by
        rw [Nat.add_zero] at halt
        exact halt
      exact False.elim (Nat.lt_irrefl d (Nat.lt_of_le_of_lt hda alt))
  | succ fuel ih =>
      unfold minFactorNatFrom
      by_cases hdn : d ≤ n
      · rw [if_pos hdn]
        cases found : natFactorSearch n d with
        | some q =>
          exact hda
        | none =>
          have dLtA : d < a := by
            exact Nat.lt_of_le_of_ne hda (fun same => by
              cases same
              cases factorAN with
              | intro q product =>
                  have qLeN : q ≤ n :=
                    NatFactor_witness_le_product
                      (Nat.lt_of_lt_of_le (by decide : 0 < 2) hd) product
                  exact natFactorSearch_none_no_factor_bounded found qLeN product)
          have succLeA : d + 1 ≤ a := Nat.succ_le_of_lt dLtA
          have aLtNext : a < d + 1 + fuel := by
            have sumEq : d + (fuel + 1) = d + 1 + fuel := by
              rw [Nat.add_assoc, Nat.add_comm fuel 1]
            exact Nat.lt_of_lt_of_eq halt sumEq
          exact ih (d + 1) (Nat.le_trans hd (Nat.le_succ d)) succLeA aLtNext
      · rw [if_neg hdn]
        have aLeN : a ≤ n := NatFactor_factor_le_of_nonzero_product hn
          (Nat.le_trans (by decide : 1 ≤ 2) (Nat.le_trans hd hda)) factorAN
        exact False.elim (hdn (Nat.le_trans hda aLeN))

theorem minFactorNat_minimal {n a : Nat} :
    2 ≤ n -> 2 ≤ a -> a ≤ n -> NatFactor a n -> minFactorNat n ≤ a := by
  intro hn ha han factorAN
  unfold minFactorNat
  have aLtSearch : a < 2 + n := by
    have nLtSearch : n < 2 + n := Nat.lt_add_of_pos_left (by decide : 0 < 2)
    exact Nat.lt_of_le_of_lt han nLtSearch
  exact minFactorNatFrom_minimal n n 2 a hn (Nat.le_refl 2) ha
    aLtSearch factorAN

theorem minFactorNat_prime {n : Nat} :
    2 ≤ n ->
      2 ≤ minFactorNat n ∧
        ∀ d : Nat, 2 ≤ d -> d < minFactorNat n -> NatFactor d (minFactorNat n) -> False := by
  intro hn
  have bound := minFactorNat_bound hn
  constructor
  · exact bound.left
  · intro d hd dLt dividesDM
    have mfDivN := minFactorNat_factor (n := n)
    have dDivN : NatFactor d n := NatFactor_trans dividesDM mfDivN
    have dLeMf : d ≤ minFactorNat n := NatFactor_factor_le_of_nonzero_product
      bound.left (Nat.le_trans (by decide : 1 ≤ 2) hd) dividesDM
    have dLeMf := minFactorNat_minimal hn hd
      (Nat.le_trans dLeMf bound.right)
      dDivN
    exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt dLeMf dLt)

private theorem unary_hsame_of_length {h k : BHist} :
    UnaryHistory h -> UnaryHistory k -> bwordLength h = bwordLength k -> hsame h k := by
  intro hUnary kUnary lengthEq
  exact (NatUp_unary_standard_bridge.right.right.right.left hUnary kUnary).mpr lengthEq

private theorem natToUnary_hsame_of_length {h : BHist} :
    UnaryHistory h -> hsame (natToUnary (bwordLength h)) h := by
  intro hUnary
  exact unary_hsame_of_length (natToUnary_unary _) hUnary (natToUnary_length _)

private theorem NatUnaryStrictPrefix_of_length_lt {h k : BHist} :
    UnaryHistory h -> UnaryHistory k -> bwordLength h < bwordLength k ->
      NatUnaryStrictPrefix h k := by
  intro hUnary kUnary lengthLt
  have total := NatUnaryPrefix_total hUnary kUnary
  cases total with
  | inl left =>
      cases left with
      | intro tail tailData =>
          cases NatUnaryPrefix_cont_tail_cases tailData.left tailData.right with
          | inl same =>
              have lengthEq : bwordLength h = bwordLength k :=
                (NatUp_unary_standard_bridge.right.right.right.left hUnary kUnary).mp same
              rw [lengthEq] at lengthLt
              exact False.elim (Nat.lt_irrefl _ lengthLt)
          | inr strict =>
              exact strict
  | inr right =>
      cases right with
      | intro tail tailData =>
          cases NatUnaryPrefix_cont_tail_cases tailData.left tailData.right with
          | inl same =>
              have lengthEq : bwordLength h = bwordLength k :=
                (NatUp_unary_standard_bridge.right.right.right.left hUnary kUnary).mp
                  (hsame_symm same)
              rw [lengthEq] at lengthLt
              exact False.elim (Nat.lt_irrefl _ lengthLt)
          | inr strictKH =>
              have kLtH := NatUnaryStrictPrefix_length_lt kUnary strictKH
              exact False.elim (Nat.lt_asymm lengthLt kLtH)

private theorem strict_unit_length_ge_two {n : BHist} :
    UnaryHistory n -> NatUnaryStrictPrefix NatOne n -> 2 ≤ bwordLength n := by
  intro nUnary strict
  have unitLt := NatUnaryStrictPrefix_length_lt (unary_e1_closed unary_empty) strict
  rw [NatUp_unary_standard_bridge.right.left BHist.Empty unary_empty] at unitLt
  exact Nat.succ_le_of_lt unitLt

private theorem natToUnary_mul_rel (a b : Nat) :
    NatMul (natToUnary a) (natToUnary b) (natToUnary (a * b)) := by
  have total := NatMul_total (natToUnary_unary a) (natToUnary_unary b)
  cases total with
  | intro result resultData =>
      have sameResult : hsame result (natToUnary (a * b)) :=
        unary_hsame_of_length resultData.left (natToUnary_unary _)
          ((NatMul_bwordLength resultData.right).trans (by
            rw [natToUnary_length, natToUnary_length, natToUnary_length]))
      exact (NatMul_result_hsame_transport resultData.right sameResult).right

theorem minFactor_divides {n : BHist} (large : NatUnaryStrictPrefix NatOne n) :
    NatDivides (minFactor n large) n := by
  have nUnary : UnaryHistory n := NatUnaryStrictPrefix_target_unary
    (unary_e1_closed unary_empty) large
  have hn : 2 ≤ bwordLength n := strict_unit_length_ge_two nUnary large
  have factorNat := minFactorNat_factor (n := bwordLength n)
  cases factorNat with
  | intro q hq =>
      have qUnary := natToUnary_unary q
      have rawMul : NatMul (natToUnary (minFactorNat (bwordLength n))) (natToUnary q)
          (natToUnary (minFactorNat (bwordLength n) * q)) :=
        natToUnary_mul_rel _ _
      have productSame : hsame (natToUnary (minFactorNat (bwordLength n) * q)) n := by
        exact unary_hsame_of_length (natToUnary_unary _) nUnary (by
          rw [natToUnary_length]
          exact hq.symm)
      exact ⟨natToUnary q, qUnary,
        (NatMul_result_hsame_transport rawMul productSame).right⟩

theorem minFactor_prime {n : BHist} (large : NatUnaryStrictPrefix NatOne n) :
    NatPrime (minFactor n large) := by
  have nUnary : UnaryHistory n := NatUnaryStrictPrefix_target_unary
    (unary_e1_closed unary_empty) large
  have hn : 2 ≤ bwordLength n := strict_unit_length_ge_two nUnary large
  have primeNat := minFactorNat_prime hn
  constructor
  · exact natToUnary_unary _
  · constructor
    · have unitLen : bwordLength NatOne < bwordLength (minFactor n large) := by
        unfold minFactor
        rw [NatUp_unary_standard_bridge.right.left BHist.Empty unary_empty, natToUnary_length]
        exact primeNat.left
      exact NatUnaryStrictPrefix_of_length_lt (unary_e1_closed unary_empty)
        (natToUnary_unary _) unitLen
    · intro d dUnary divides
      have dLenPosCases := Nat.eq_zero_or_pos (bwordLength d)
      cases dLenPosCases with
      | inl dZero =>
          have dEmpty : hsame d BHist.Empty :=
            unary_hsame_of_length dUnary unary_empty (dZero.trans NatUp_unary_standard_bridge.left.symm)
          have mfEmpty := NatDivides_empty_left_result_empty
            ((NatDivides_divisor_hsame_transport divides dEmpty).right)
          unfold minFactor at mfEmpty
          have mfLenZero : minFactorNat (bwordLength n) = 0 := by
            have lenEq := congrArg bwordLength mfEmpty
            rw [natToUnary_length, NatUp_unary_standard_bridge.left] at lenEq
            exact lenEq
          exact False.elim (Nat.not_succ_le_zero 1 (mfLenZero ▸ primeNat.left))
      | inr dPos =>
          by_cases dLenOne : bwordLength d = 1
          · have sameUnit : hsame d NatOne := by
              exact unary_hsame_of_length dUnary (unary_e1_closed unary_empty) (by
                rw [dLenOne]
                exact (NatUp_unary_standard_bridge.right.left BHist.Empty unary_empty).symm)
            exact Or.inl sameUnit
          · have twoLeD : 2 ≤ bwordLength d := by
              cases hlen : bwordLength d with
              | zero =>
                  rw [hlen] at dPos
                  exact False.elim (Nat.lt_irrefl 0 dPos)
              | succ dPred =>
                  cases dPred with
                  | zero =>
                      exact False.elim (dLenOne hlen)
                  | succ dTail =>
                      exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le dTail))
            have dividesLen : NatFactor (bwordLength d) (minFactorNat (bwordLength n)) := by
              cases divides with
              | intro q qData =>
                  have mulLen := NatMul_bwordLength qData.right
                  unfold minFactor at mulLen
                  rw [natToUnary_length] at mulLen
                  exact ⟨bwordLength q, mulLen⟩
            have dLeMfLen : bwordLength d ≤ minFactorNat (bwordLength n) :=
              NatFactor_factor_le_of_nonzero_product primeNat.left
                (Nat.le_trans (by decide : 1 ≤ 2) twoLeD) dividesLen
            by_cases sameLen : bwordLength d = minFactorNat (bwordLength n)
            · exact Or.inr (by
                unfold minFactor
                exact unary_hsame_of_length dUnary (natToUnary_unary _) (by
                  rw [sameLen, natToUnary_length]))
            · have dLtMf := Nat.lt_of_le_of_ne dLeMfLen sameLen
              exact False.elim (primeNat.right (bwordLength d) twoLeD dLtMf dividesLen)

private theorem unary_nonunit_length_ge_two {m : BHist} :
    UnaryHistory m -> (hsame m BHist.Empty -> False) ->
      (hsame m NatOne -> False) -> 2 ≤ bwordLength m := by
  intro mUnary mNonempty mNonunit
  cases m with
  | Empty =>
      exact False.elim (mNonempty rfl)
  | e0 tail =>
      cases mUnary
  | e1 tail =>
      cases tail with
      | Empty =>
          exact False.elim (mNonunit (hsame_refl NatOne))
      | e0 inner =>
          cases unary_e1_inversion mUnary
      | e1 inner =>
          exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le (bwordLength inner)))

private theorem unit_or_not_unit (m : BHist) :
    hsame m NatOne ∨ (hsame m NatOne -> False) := by
  cases m with
  | Empty =>
      exact Or.inr (fun same => not_hsame_emp_e1 same)
  | e0 tail =>
      exact Or.inr (fun same => not_hsame_e0_e1 same)
  | e1 tail =>
      cases tail with
      | Empty =>
          exact Or.inl (hsame_refl NatOne)
      | e0 inner =>
          exact Or.inr (fun same => by cases same)
      | e1 inner =>
          exact Or.inr (fun same => by cases same)

private theorem NatMul_right_factor_strict_of_prime_left {p m n : BHist} :
    NatPrime p -> UnaryHistory m -> NatMul p m n ->
      (hsame m BHist.Empty -> False) -> (hsame m NatOne -> False) ->
        NatUnaryStrictPrefix m n := by
  intro pPrime mUnary mul mNonempty mNonunit
  have nUnary : UnaryHistory n := NatMul_result_unary pPrime.left mul
  have pLenGeTwo : 2 ≤ bwordLength p := strict_unit_length_ge_two pPrime.left pPrime.right.left
  have mLenGeTwo : 2 ≤ bwordLength m := unary_nonunit_length_ge_two mUnary mNonempty mNonunit
  have mLenPos : 0 < bwordLength m :=
    Nat.lt_of_lt_of_le (by decide : 0 < 2) mLenGeTwo
  have oneLtP : 1 < bwordLength p := pLenGeTwo
  have strictLen : bwordLength m < bwordLength n := by
    have raw : 1 * bwordLength m < bwordLength p * bwordLength m :=
      Nat.mul_lt_mul_of_pos_right oneLtP mLenPos
    rw [Nat.one_mul] at raw
    exact Nat.lt_of_lt_of_eq raw (NatMul_bwordLength mul).symm
  exact NatUnaryStrictPrefix_of_length_lt mUnary nUnary strictLen

private theorem factor_witness_of_divides {d n : BHist} :
    NatDivides d n -> ∃ q : BHist, UnaryHistory q ∧ NatMul d q n := by
  intro divides
  exact divides

private theorem factorization_prefix {p m n : BHist} {factors : List BHist} :
    NatPrime p -> PrimeFactorization m factors -> NatMul p m n ->
      PrimeFactorization n (p :: factors) := by
  intro pPrime factorization mul
  exact ⟨NatMul_result_unary pPrime.left mul, pPrime,
    ⟨m, factorization.right, mul⟩⟩

theorem factorize_unit :
    ∃ entries : List BHist, PrimeFactorization NatOne entries ∧ hsame NatOne NatOne := by
  exact ⟨[], ⟨unary_e1_closed unary_empty, hsame_refl NatOne⟩, hsame_refl NatOne⟩

theorem factorize (n : BHist) (large : NatUnaryStrictPrefix NatOne n) :
    ∃ entries : List BHist, PrimeFactorization n entries ∧ hsame n n := by
  have nUnary : UnaryHistory n := NatUnaryStrictPrefix_target_unary
    (unary_e1_closed unary_empty) large
  have nNonempty : hsame n BHist.Empty -> False := by
    intro nEmpty
    exact NatUnaryStrictPrefix_empty_right_absurd
      (NatUnaryStrictPrefix_hsame_target_transport_for_divides_closure large nEmpty)
  revert large
  refine NatStrongInduction
    (P := fun x => NatUnaryStrictPrefix NatOne x ->
      ∃ entries : List BHist, PrimeFactorization x entries ∧ hsame x x) ?_ n nUnary
  intro x xUnary ih xLarge
  let p := minFactor x xLarge
  have pPrime : NatPrime p := minFactor_prime xLarge
  have pDivides : NatDivides p x := minFactor_divides xLarge
  cases factor_witness_of_divides pDivides with
  | intro m mData =>
      have mUnary : UnaryHistory m := mData.left
      cases m with
      | Empty =>
          have xEmpty : hsame x BHist.Empty := by
            cases mData.right
            rfl
          exact False.elim
            (NatUnaryStrictPrefix_empty_right_absurd
              (NatUnaryStrictPrefix_hsame_target_transport_for_divides_closure xLarge xEmpty))
      | e0 mTail =>
          cases mUnary
      | e1 mTail =>
          cases unit_or_not_unit (BHist.e1 mTail) with
          | inl mUnit =>
          · have shiftedMul : NatMul p NatOne x :=
              (NatMul_multiplier_hsame_transport mData.right mUnit).right
            have sameXP : hsame x p := NatMul_unit_right_hsame shiftedMul
            have product : PrimeFactorization x [p] := by
              exact ⟨xUnary, PrimeFactorizationProduct_result_hsame_transport
                (And.intro pPrime ⟨NatOne, hsame_refl NatOne,
                  NatMul.succ (NatMul.zero pPrime.left) (cont_left_unit p)⟩)
                (hsame_symm sameXP)⟩
            exact ⟨[p], product, hsame_refl x⟩
          | inr mNonunit =>
          · have mStrict : NatUnaryStrictPrefix (BHist.e1 mTail) x :=
              NatMul_right_factor_strict_of_prime_left pPrime mUnary mData.right
                (fun empty => not_hsame_e1_empty empty) mNonunit
            have mLarge : NatUnaryStrictPrefix NatOne (BHist.e1 mTail) :=
              NatUnaryStrictPrefix_of_length_lt (unary_e1_closed unary_empty) mUnary (by
                have mGeTwo := unary_nonunit_length_ge_two mUnary
                  (fun empty => not_hsame_e1_empty empty) mNonunit
                rw [NatUp_unary_standard_bridge.right.left BHist.Empty unary_empty]
                exact mGeTwo)
            have hrec := ih (BHist.e1 mTail) mUnary mStrict mLarge
            cases hrec with
            | intro entries recData =>
                exact ⟨p :: entries,
                  factorization_prefix pPrime recData.left mData.right,
                  hsame_refl x⟩

theorem factorization_unique_via_padic {p n k l : BHist} :
    IsPadicValNat p n k -> IsPadicValNat p n l -> hsame k l := by
  intro left right
  exact IsPadicValNat_unique left right

def ListPermPrime (ps qs : List BHist) : Prop :=
  List.Perm ps qs

theorem prime_divides_product_mem {p n : BHist} {qs : List BHist} :
    NatPrime p -> PrimeFactorizationProduct qs n -> NatDivides p n ->
      ∃ q : BHist, q ∈ qs ∧ hsame p q := by
  intro pPrime product divides
  induction qs generalizing n with
  | nil =>
      have dividesUnit : NatDivides p NatOne :=
        (NatDivides_dividend_hsame_transport divides product).right
      have pUnit : hsame p NatOne := NatDivides_unit_right_iff.mp dividesUnit
      cases pUnit
      exact False.elim (NatPrime_unit_absurd pPrime)
  | cons q qs ih =>
      cases product with
      | intro qPrime tailWitness =>
          cases tailWitness with
          | intro tailProduct tailData =>
              have tailUnary : UnaryHistory tailProduct :=
                PrimeFactorizationProduct_result_unary tailData.left
              have split :=
                NatEuclidPrime_product_left_or_right
                  (NatPrime.toNatEuclidPrime pPrime) qPrime.left tailUnary
                  tailData.right divides
              cases split with
              | inl dividesQ =>
                  cases qPrime.right.right p pPrime.left dividesQ with
                  | inl pUnit =>
                      cases pUnit
                      exact False.elim (NatPrime_unit_absurd pPrime)
                  | inr samePQ =>
                      exact ⟨q, List.Mem.head qs, samePQ⟩
              | inr dividesTail =>
                  cases ih tailData.left dividesTail with
                  | intro r rData =>
                      exact ⟨r, List.Mem.tail q rData.left, rData.right⟩

private theorem NatMul_middle_swap_result {p q r pr n qr : BHist} :
    UnaryHistory p -> UnaryHistory q -> UnaryHistory r ->
      NatMul p r pr -> NatMul q pr n -> NatMul q r qr -> NatMul p qr n := by
  intro pUnary qUnary rUnary productPR productQPR productQR
  cases NatMul_total qUnary pUnary with
  | intro qp qpData =>
      cases NatMul_total pUnary qUnary with
      | intro pq pqData =>
          cases NatMul_total qpData.left rUnary with
          | intro qpr qprData =>
              cases NatMul_total pqData.left rUnary with
              | intro pqr pqrData =>
                  cases NatMul_total pUnary (NatMul_result_unary qUnary productQR) with
                  | intro displayed displayedData =>
                      have sameQPRN : hsame qpr n :=
                        NatMul_assoc_hsame qUnary pUnary rUnary qpData.right
                          qprData.right productPR productQPR
                      have sameQPPQ : hsame qp pq :=
                        NatMul_comm_hsame qUnary pUnary qpData.right pqData.right
                      have productPQRAtQPR : NatMul pq r qpr :=
                        (NatMul_multiplicand_hsame_transport sameQPPQ qprData.right).right
                      have sameQPRPQR : hsame qpr pqr :=
                        NatMul_functional pqData.left productPQRAtQPR pqrData.right
                      have samePQRDisplayed : hsame pqr displayed :=
                        NatMul_assoc_hsame pUnary qUnary rUnary pqData.right
                          pqrData.right productQR displayedData.right
                      have sameDisplayedN : hsame displayed n :=
                        hsame_trans (hsame_symm samePQRDisplayed)
                          (hsame_trans (hsame_symm sameQPRPQR) sameQPRN)
                      exact
                        (NatMul_result_hsame_transport displayedData.right sameDisplayedN).right

theorem factorization_extract_mem {p n : BHist} {qs : List BHist} :
    NatPrime p -> PrimeFactorizationProduct qs n ->
      (∃ q : BHist, q ∈ qs ∧ hsame p q) ->
        ∃ qs' : List BHist, ∃ tailProduct : BHist,
          ListPermPrime qs (p :: qs') ∧
            PrimeFactorizationProduct qs' tailProduct ∧ NatMul p tailProduct n := by
  intro pPrime product member
  induction qs generalizing n with
  | nil =>
      cases member with
      | intro q qData =>
          cases qData.left
  | cons q qs ih =>
      cases product with
      | intro qPrime tailWitness =>
          cases tailWitness with
          | intro tailProduct tailData =>
              cases member with
              | intro r rData =>
                  cases rData.left with
                  | head =>
                      have samePQ : hsame p q := rData.right
                      have productAtP : NatMul p tailProduct n :=
                        (NatMul_multiplicand_hsame_transport
                          (hsame_symm samePQ) tailData.right).right
                      have permHead : ListPermPrime (q :: qs) (p :: qs) := by
                        cases samePQ
                        exact List.Perm.refl (p :: qs)
                      exact ⟨qs, tailProduct, permHead, tailData.left, productAtP⟩
                  | tail _ tailMember =>
                      have tailMemberWitness :
                          ∃ s : BHist, s ∈ qs ∧ hsame p s :=
                        ⟨r, tailMember, rData.right⟩
                      cases ih tailData.left tailMemberWitness with
                      | intro qs' extracted =>
                          cases extracted with
                          | intro restProduct extractedData =>
                              have restUnary : UnaryHistory restProduct :=
                                PrimeFactorizationProduct_result_unary extractedData.right.left
                              cases NatMul_total qPrime.left restUnary with
                              | intro qRest qRestData =>
                                  have productQRest :
                                      PrimeFactorizationProduct (q :: qs') qRest :=
                                    And.intro qPrime
                                      ⟨restProduct, extractedData.right.left,
                                        qRestData.right⟩
                                  have productPAtN : NatMul p qRest n :=
                                    NatMul_middle_swap_result pPrime.left qPrime.left
                                      restUnary extractedData.right.right tailData.right
                                      qRestData.right
                                  have permCons :
                                      ListPermPrime (q :: qs) (q :: p :: qs') :=
                                    List.Perm.cons q extractedData.left
                                  have permSwap :
                                      ListPermPrime (q :: p :: qs') (p :: q :: qs') :=
                                    List.Perm.swap p q qs'
                                  exact ⟨q :: qs', qRest,
                                    List.Perm.trans permCons permSwap,
                                    productQRest, productPAtN⟩

theorem factorization_remove_hsame {p n : BHist} {ps qs : List BHist} :
    PrimeFactorizationProduct (p :: ps) n -> PrimeFactorizationProduct qs n ->
      (∃ q : BHist, q ∈ qs ∧ hsame p q) ->
        ∃ qs' : List BHist, ∃ tailProduct : BHist,
          ListPermPrime qs (p :: qs') ∧
            PrimeFactorizationProduct ps tailProduct ∧
              PrimeFactorizationProduct qs' tailProduct := by
  intro left right member
  cases left with
  | intro pPrime leftTail =>
      cases leftTail with
      | intro leftTailProduct leftData =>
          cases factorization_extract_mem pPrime right member with
          | intro qs' extracted =>
              cases extracted with
              | intro rightTailProduct extractedData =>
                  have sameTail : hsame leftTailProduct rightTailProduct :=
                    NatMul_nonempty_multiplicand_result_cancel pPrime.left
                      (NatPrime_empty_absurd pPrime) leftData.right
                      extractedData.right.right (hsame_refl n)
                  have rightTailProductAtLeft :
                      PrimeFactorizationProduct qs' leftTailProduct :=
                    PrimeFactorizationProduct_result_hsame_transport
                      extractedData.right.left (hsame_symm sameTail)
                  exact ⟨qs', leftTailProduct, extractedData.left, leftData.left,
                    rightTailProductAtLeft⟩

theorem factorization_remove {p n : BHist} {ps qs : List BHist} :
    PrimeFactorizationProduct (p :: ps) n -> PrimeFactorizationProduct qs n ->
      p ∈ qs ->
        ∃ qs' : List BHist, ∃ tailProduct : BHist,
          ListPermPrime qs (p :: qs') ∧
            PrimeFactorizationProduct ps tailProduct ∧
              PrimeFactorizationProduct qs' tailProduct := by
  intro left right member
  exact factorization_remove_hsame left right ⟨p, member, hsame_refl p⟩

private theorem PrimeFactorizationProduct_unit_perm_nil {qs : List BHist} {n : BHist} :
    PrimeFactorizationProduct qs n -> hsame n NatOne -> ListPermPrime qs [] := by
  intro product sameUnit
  cases qs with
  | nil =>
      exact List.Perm.refl []
  | cons q qs =>
      cases product with
      | intro qPrime tailWitness =>
          cases tailWitness with
          | intro tailProduct tailData =>
              have unitProduct : NatMul q tailProduct NatOne :=
                (NatMul_result_hsame_transport tailData.right sameUnit).right
              have qUnit : hsame q NatOne :=
                (NatMul_unit_result_factors_unit unitProduct).left
              cases qUnit
              exact False.elim (NatPrime_unit_absurd qPrime)

theorem factorization_unique_perm {ps qs : List BHist} {n : BHist} :
    PrimeFactorizationProduct ps n -> PrimeFactorizationProduct qs n -> ListPermPrime ps qs := by
  induction ps generalizing n qs with
  | nil =>
      intro left right
      exact List.Perm.symm (PrimeFactorizationProduct_unit_perm_nil right left)
  | cons p ps ih =>
      intro left right
      cases left with
      | intro pPrime leftTail =>
          cases leftTail with
          | intro tailProduct leftData =>
              have pDividesN : NatDivides p n :=
                ⟨tailProduct, PrimeFactorizationProduct_result_unary leftData.left,
                  leftData.right⟩
              have pMember : ∃ q : BHist, q ∈ qs ∧ hsame p q :=
                prime_divides_product_mem pPrime right pDividesN
              cases factorization_remove_hsame
                  (And.intro pPrime ⟨tailProduct, leftData.left, leftData.right⟩)
                  right pMember with
              | intro qs' removed =>
                  cases removed with
                  | intro commonTail removedData =>
                      have tailPerm : ListPermPrime ps qs' :=
                        ih removedData.right.left removedData.right.right
                      have withHead : ListPermPrime (p :: ps) (p :: qs') :=
                        List.Perm.cons p tailPerm
                      exact List.Perm.trans withHead (List.Perm.symm removedData.left)

structure FundamentalTheoremArithmetic where
  exists_factorization :
    ∀ n : BHist, NatUnaryStrictPrefix NatOne n ->
      ∃ entries : List BHist, PrimeFactorization n entries
  unique_factorization :
    ∀ {n : BHist} {ps qs : List BHist},
      PrimeFactorizationProduct ps n ->
        PrimeFactorizationProduct qs n -> ListPermPrime ps qs

theorem fundamental_theorem_arithmetic : FundamentalTheoremArithmetic := by
  constructor
  · intro n large
    cases factorize n large with
    | intro entries data =>
        exact ⟨entries, data.left⟩
  · intro n ps qs left right
    exact factorization_unique_perm left right

structure IntegerUp where
  sign : BMark
  magnitude : BHist
  carrier : IntCarrier sign magnitude

def IntegerPrimeFactorization
    (z : IntegerUp) (entries : List BHist) : Prop :=
  IntCarrier z.sign z.magnitude ∧ PrimeFactorization z.magnitude entries

theorem product_formula
    (z : IntegerUp)
    (nonzero : hsame z.magnitude BHist.Empty -> False) :
    ∃ entries : List BHist, IntegerPrimeFactorization z entries := by
  cases z with
  | mk sign magnitude carrier =>
      cases magnitude with
      | Empty =>
          exact False.elim (nonzero (hsame_refl BHist.Empty))
      | e0 tail =>
          cases carrier.right
      | e1 tail =>
          cases unit_or_not_unit (BHist.e1 tail) with
          | inl unit =>
          · exact ⟨[], carrier, ⟨carrier.right, PrimeFactorizationProduct_result_hsame_transport
                (hsame_refl NatOne) (hsame_symm unit)⟩⟩
          | inr nonunit =>
          · have large : NatUnaryStrictPrefix NatOne (BHist.e1 tail) :=
              NatUnaryStrictPrefix_of_length_lt (unary_e1_closed unary_empty) carrier.right (by
                have magGeTwo := unary_nonunit_length_ge_two carrier.right nonzero nonunit
                rw [NatUp_unary_standard_bridge.right.left BHist.Empty unary_empty]
                exact magGeTwo)
            cases factorize (BHist.e1 tail) large with
            | intro entries data =>
                exact ⟨entries, carrier, data.left⟩

theorem product_formula_nat
    (n : BHist) (large : NatUnaryStrictPrefix NatOne n) :
    ∃ entries : List BHist, PrimeFactorization n entries := by
  cases factorize n large with
  | intro entries data =>
      exact ⟨entries, data.left⟩

end BEDC.Derived.PrimeUp
