import BEDC.Derived.SumTwoSquaresUp
import BEDC.Derived.ZModUp

namespace BEDC.Derived.GaussianPrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp

abbrev Z := BEDC.Algebra.Rel.IntegerUp
abbrev Zeq := BEDC.Algebra.Rel.IntEq
abbrev Zadd := BEDC.Algebra.Rel.IntAdd
abbrev Zmul := BEDC.Algebra.Rel.IntMul
abbrev Zneg := BEDC.Algebra.Rel.IntNeg
abbrev Zzero := BEDC.Algebra.Rel.intZero
abbrev Zone := BEDC.Algebra.Rel.intOne

abbrev GaussInt := BEDC.Derived.GaussianUp.GaussInt
abbrev GaussEq := BEDC.Derived.GaussianUp.GaussEq
abbrev gaussOne := BEDC.Derived.GaussianUp.gaussOne
abbrev gaussMul := BEDC.Derived.GaussianUp.gaussMul
abbrev gaussConj := BEDC.Derived.GaussianUp.gaussConj
abbrev gaussNorm := BEDC.Derived.GaussianUp.gaussNorm
abbrev gaussOfInt := BEDC.Derived.GaussianUp.gaussOfInt

private def ZR : BEDC.Algebra.Rel.RelCommRing Z Zeq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

private def GR : BEDC.Algebra.Rel.RelCommRing GaussInt GaussEq :=
  BEDC.Algebra.Rel.GaussianUp_RelCommRing

abbrev NatTwo : BHist :=
  BHist.e1 NatOne

abbrev NatThree : BHist :=
  BHist.e1 NatTwo

abbrev NatFour : BHist :=
  BHist.e1 NatThree

def intTwo : Z :=
  Zadd Zone Zone

def intOfUnary (n : BHist) (hn : UnaryHistory n) : Z :=
  BEDC.Derived.RationalUp.intOfNat n hn

def GaussianUnit (u : GaussInt) : Prop :=
  ∃ v : GaussInt, GaussEq (gaussMul u v) gaussOne

def GaussianDivides (a b : GaussInt) : Prop :=
  ∃ c : GaussInt, GaussEq (gaussMul a c) b

def GaussianAssociated (a b : GaussInt) : Prop :=
  ∃ u : GaussInt, GaussianUnit u ∧ GaussEq a (gaussMul u b)

def GaussianIrreducible (z : GaussInt) : Prop :=
  (GaussianUnit z -> False) ∧
    ∀ a b : GaussInt, GaussEq (gaussMul a b) z ->
      GaussianUnit a ∨ GaussianUnit b

def GaussianPrime (z : GaussInt) : Prop :=
  GaussianIrreducible z

def IntegerUnit (n : Z) : Prop :=
  ∃ m : Z, Zeq (Zmul n m) Zone

def IntegerMultiplicativePrime (n : Z) : Prop :=
  (IntegerUnit n -> False) ∧
    ∀ a b : Z, Zeq (Zmul a b) n -> IntegerUnit a ∨ IntegerUnit b

def NormUnitReflectsGaussianUnit : Prop :=
  ∀ z : GaussInt, IntegerUnit (gaussNorm z) -> GaussianUnit z

def NatCongruentOneModFour (p : BHist) : Prop :=
  hsame (natModFn NatFour p) NatOne

def NatCongruentThreeModFour (p : BHist) : Prop :=
  hsame (natModFn NatFour p) NatThree

def GaussianSplit (p : Z) : Prop :=
  ∃ z : GaussInt, GaussEq (gaussMul z (gaussConj z)) (gaussOfInt p)

def NoSumTwoSquares (p : Z) : Prop :=
  BEDC.Derived.SumTwoSquaresUp.IsSumTwoSquares p -> False

def FermatTwoSquaresBridge (p : BHist) (hp : UnaryHistory p) : Prop :=
  NatPrime p -> NatCongruentOneModFour p ->
    BEDC.Derived.SumTwoSquaresUp.IsSumTwoSquares (intOfUnary p hp)

def ModThreeNoTwoSquaresBridge (p : BHist) (hp : UnaryHistory p) : Prop :=
  NatPrime p -> NatCongruentThreeModFour p ->
    NoSumTwoSquares (intOfUnary p hp)

def RationalPrimeGaussianFactorAlternative (p : Z) : Prop :=
  ∀ a b : GaussInt, GaussEq (gaussMul a b) (gaussOfInt p) ->
    IntegerUnit (gaussNorm a) ∨
      IntegerUnit (gaussNorm b) ∨
        BEDC.Derived.SumTwoSquaresUp.IsSumTwoSquares p

theorem gaussOfInt_respects {a b : Z} :
    Zeq a b -> GaussEq (gaussOfInt a) (gaussOfInt b) := by
  intro h
  constructor
  · exact h
  · exact ZR.refl Zzero

theorem gaussNorm_one :
    Zeq (gaussNorm gaussOne) Zone := by
  exact ZR.trans
    (ZR.add_congr (ZR.mul_one Zone) (ZR.mul_zero Zzero))
    (ZR.add_zero Zone)

theorem gaussianUnit_norm_integerUnit {u : GaussInt} :
    GaussianUnit u -> IntegerUnit (gaussNorm u) := by
  intro unitU
  cases unitU with
  | intro v productOne =>
      exact ⟨gaussNorm v,
        ZR.trans
          (ZR.symm (BEDC.Derived.GaussianUp.gaussNorm_mul u v))
          (ZR.trans
            (BEDC.Derived.GaussianUp.gaussNorm_respects productOne)
            gaussNorm_one)⟩

theorem int_norm_prime_factor_units {z a b : GaussInt} :
    IntegerMultiplicativePrime (gaussNorm z) ->
      GaussEq (gaussMul a b) z ->
        IntegerUnit (gaussNorm a) ∨ IntegerUnit (gaussNorm b) := by
  intro normPrime productZ
  exact normPrime.right (gaussNorm a) (gaussNorm b)
    (ZR.trans
      (ZR.symm (BEDC.Derived.GaussianUp.gaussNorm_mul a b))
      (BEDC.Derived.GaussianUp.gaussNorm_respects productZ))

theorem int_norm_prime_implies_gaussian_prime {z : GaussInt} :
    IntegerMultiplicativePrime (gaussNorm z) ->
      NormUnitReflectsGaussianUnit ->
        GaussianPrime z := by
  intro normPrime unitReflect
  constructor
  · intro unitZ
    exact normPrime.left (gaussianUnit_norm_integerUnit unitZ)
  · intro a b productZ
    cases int_norm_prime_factor_units normPrime productZ with
    | inl unitNormA =>
        exact Or.inl (unitReflect a unitNormA)
    | inr unitNormB =>
        exact Or.inr (unitReflect b unitNormB)

def gaussianOnePlusI : GaussInt :=
  { re := Zone, im := Zone }

def gaussianOneMinusI : GaussInt :=
  gaussConj gaussianOnePlusI

theorem gaussNorm_one_plus_i :
    Zeq (gaussNorm gaussianOnePlusI) intTwo := by
  exact ZR.add_congr (ZR.mul_one Zone) (ZR.mul_one Zone)

theorem gaussian_two_ramifies :
    GaussEq (gaussMul gaussianOnePlusI gaussianOneMinusI)
      (gaussOfInt intTwo) := by
  exact GR.trans (BEDC.Derived.GaussianUp.gaussMul_conj_norm gaussianOnePlusI)
    (gaussOfInt_respects gaussNorm_one_plus_i)

theorem sum_two_squares_splits {p : Z} :
    BEDC.Derived.SumTwoSquaresUp.IsSumTwoSquares p ->
      GaussianSplit p := by
  intro represented
  cases represented with
  | intro a rest =>
      cases rest with
      | intro b witness =>
          let z := BEDC.Derived.SumTwoSquaresUp.gaussianPair a b
          have normShape :
              Zeq (gaussNorm z) p := by
            exact ZR.trans
              (BEDC.Derived.SumTwoSquaresUp.gaussianPair_norm a b)
              (ZR.symm witness)
          exact ⟨z,
            GR.trans
              (BEDC.Derived.GaussianUp.gaussMul_conj_norm z)
              (gaussOfInt_respects normShape)⟩

theorem rational_prime_split_of_congruent_one_mod_four
    {p : BHist} (hp : UnaryHistory p) :
    NatPrime p ->
      NatCongruentOneModFour p ->
        FermatTwoSquaresBridge p hp ->
          GaussianSplit (intOfUnary p hp) := by
  intro primeP pMod bridge
  exact sum_two_squares_splits (bridge primeP pMod)

theorem rational_prime_inert_of_congruent_three_mod_four
    {p : BHist} (hp : UnaryHistory p) :
    NatPrime p ->
      NatCongruentThreeModFour p ->
        ModThreeNoTwoSquaresBridge p hp ->
          RationalPrimeGaussianFactorAlternative (intOfUnary p hp) ->
            (GaussianUnit (gaussOfInt (intOfUnary p hp)) -> False) ->
              NormUnitReflectsGaussianUnit ->
                GaussianPrime (gaussOfInt (intOfUnary p hp)) := by
  intro primeP pMod noSquaresBridge factorAlternative rationalPrimeNonunit unitReflect
  constructor
  · exact rationalPrimeNonunit
  · intro a b productP
    have noSquares : NoSumTwoSquares (intOfUnary p hp) :=
      noSquaresBridge primeP pMod
    cases factorAlternative a b productP with
    | inl unitNormA =>
        exact Or.inl (unitReflect a unitNormA)
    | inr tail =>
        cases tail with
        | inl unitNormB =>
            exact Or.inr (unitReflect b unitNormB)
        | inr sumSquares =>
            exact False.elim (noSquares sumSquares)

open BEDC.FKernel.ExternalBinary (bwordLength bwordLength_append)
open BEDC.Derived.RationalUp (intToPair pairToInt intOfNat intAdd intMul
  intToPair_carrier intAdd_pair_classifier intToPair_pairToInt_classifier)
open BEDC.Derived.IntUp (IntPairClassifier IntPairCarrier pairAdd pairMul
  natMulFn natMulFn_bwordLength pairMul_carrier)

-- The mod-four square obstruction is developed with propext/Quot.sound-free
-- native-Nat arithmetic: no `omega`, no `Nat.mul_mod`/`Nat.div_add_mod`
-- (each of those transitively depends on `propext`). Only pure induction and
-- the pure `Nat` ring/order lemmas are used, so every declaration below stays
-- inside the BEDC zero-stdlib-axiom invariant.

private theorem add_right_cancel_pure : ∀ (a b c : Nat), a + c = b + c → a = b := by
  intro a b c
  induction c with
  | zero => intro h; exact h
  | succ n ih => intro h; exact ih (Nat.succ.inj h)

private theorem mul_assoc_pure : ∀ (a b c : Nat), a * b * c = a * (b * c) := by
  intro a b c
  induction c with
  | zero => rfl
  | succ n ih => rw [Nat.mul_succ, Nat.mul_succ, Nat.mul_add, ih]

private theorem add_mul_pure (a b c : Nat) : (a + b) * c = a * c + b * c := by
  rw [Nat.mul_comm (a + b) c, Nat.mul_add, Nat.mul_comm c a, Nat.mul_comm c b]

private theorem parity : ∀ n : Nat, ∃ m, n = 2 * m ∨ n = 2 * m + 1 := by
  intro n
  induction n with
  | zero => exact ⟨0, Or.inl rfl⟩
  | succ k ih =>
      cases ih with
      | intro m hm =>
          cases hm with
          | inl he => exact ⟨m, Or.inr (by rw [he])⟩
          | inr ho => exact ⟨m + 1, Or.inl (by rw [ho, Nat.mul_succ])⟩

private theorem even_sq (m : Nat) : (2 * m) * (2 * m) = 4 * (m * m) := by
  rw [mul_assoc_pure, Nat.mul_comm m (2 * m), mul_assoc_pure]
  exact (mul_assoc_pure 2 2 (m * m)).symm

private theorem odd_sq (m : Nat) :
    (2 * m + 1) * (2 * m + 1) = 4 * (m * m + m) + 1 := by
  have h1 : (2 * m + 1) * (2 * m + 1) = (2 * m) * (2 * m + 1) + (2 * m + 1) := by
    rw [add_mul_pure, Nat.one_mul]
  have h2 : (2 * m) * (2 * m + 1) = 4 * (m * m) + 2 * m := by
    rw [Nat.mul_add, Nat.mul_one, even_sq]
  have h3 : 2 * m + 2 * m = 4 * m := (add_mul_pure 2 2 m).symm
  rw [h1, h2, Nat.mul_add, Nat.add_assoc (4 * (m * m)) (2 * m),
    ← Nat.add_assoc (2 * m) (2 * m) 1, h3, ← Nat.add_assoc]

private theorem sq_quarter : ∀ n : Nat, ∃ m, n * n = 4 * m ∨ n * n = 4 * m + 1 := by
  intro n
  cases parity n with
  | intro k hk =>
      cases hk with
      | inl he => exact ⟨k * k, Or.inl (by rw [he, even_sq])⟩
      | inr ho => exact ⟨k * k + k, Or.inr (by rw [ho, odd_sq])⟩

private theorem regroup0 (a b : Nat) : 4 * a + 4 * b = 4 * (a + b) :=
  (Nat.mul_add 4 a b).symm

private theorem regroup1 (a b : Nat) : 4 * a + (4 * b + 1) = 4 * (a + b) + 1 := by
  rw [← Nat.add_assoc, regroup0]

private theorem regroup2 (a b : Nat) : (4 * a + 1) + 4 * b = 4 * (a + b) + 1 := by
  rw [Nat.add_assoc, Nat.add_comm 1 (4 * b), ← Nat.add_assoc, regroup0]

private theorem regroup3 (a b : Nat) : (4 * a + 1) + (4 * b + 1) = 4 * (a + b) + 2 := by
  rw [Nat.add_assoc, Nat.add_comm 1 (4 * b + 1), Nat.add_assoc,
    ← Nat.add_assoc (4 * a), regroup0]

private theorem quad_rem_uniq : ∀ (A B r s : Nat), r < 4 → s < 4 →
    4 * A + r = 4 * B + s → r = s := by
  intro A
  induction A with
  | zero =>
      intro B r s hr hs h
      cases B with
      | zero => rw [Nat.mul_zero, Nat.zero_add, Nat.zero_add] at h; exact h
      | succ B' =>
          exfalso
          rw [Nat.mul_zero, Nat.zero_add] at h
          have hge : 4 ≤ 4 * (B' + 1) + s := by
            have h4 : 4 * 1 ≤ 4 * (B' + 1) :=
              Nat.mul_le_mul_left 4 (Nat.succ_le_succ (Nat.zero_le B'))
            exact Nat.le_trans h4 (Nat.le_add_right _ _)
          rw [h] at hr
          exact Nat.lt_irrefl 4 (Nat.lt_of_le_of_lt hge hr)
  | succ A' ih =>
      intro B r s hr hs h
      cases B with
      | zero =>
          exfalso
          rw [Nat.mul_zero, Nat.zero_add] at h
          have hge : 4 ≤ 4 * (A' + 1) + r := by
            have h4 : 4 * 1 ≤ 4 * (A' + 1) :=
              Nat.mul_le_mul_left 4 (Nat.succ_le_succ (Nat.zero_le A'))
            exact Nat.le_trans h4 (Nat.le_add_right _ _)
          rw [h] at hge
          exact Nat.lt_irrefl 4 (Nat.lt_of_le_of_lt hge hs)
      | succ B' =>
          apply ih B' r s hr hs
          rw [Nat.mul_succ, Nat.mul_succ] at h
          apply add_right_cancel_pure (4 * A' + r) (4 * B' + s) 4
          calc 4 * A' + r + 4 = 4 * A' + 4 + r := by rw [Nat.add_right_comm]
            _ = 4 * B' + 4 + s := h
            _ = 4 * B' + s + 4 := by rw [Nat.add_right_comm]

theorem natSumTwoSquares_mod_four_obstruction (x y q : Nat) :
    x * x + y * y = 4 * q + 3 -> False := by
  intro balance
  cases sq_quarter x with
  | intro mx hx =>
      cases sq_quarter y with
      | intro my hy =>
          cases hx with
          | inl hx0 =>
              cases hy with
              | inl hy0 =>
                  rw [hx0, hy0, regroup0] at balance
                  exact absurd
                    (quad_rem_uniq (mx + my) q 0 3 (by decide) (by decide)
                      (by rw [Nat.add_zero]; exact balance)) (by decide)
              | inr hy1 =>
                  rw [hx0, hy1, regroup1] at balance
                  exact absurd
                    (quad_rem_uniq (mx + my) q 1 3 (by decide) (by decide) balance)
                    (by decide)
          | inr hx1 =>
              cases hy with
              | inl hy0 =>
                  rw [hx1, hy0, regroup2] at balance
                  exact absurd
                    (quad_rem_uniq (mx + my) q 1 3 (by decide) (by decide) balance)
                    (by decide)
              | inr hy1 =>
                  rw [hx1, hy1, regroup3] at balance
                  exact absurd
                    (quad_rem_uniq (mx + my) q 2 3 (by decide) (by decide) balance)
                    (by decide)

-- Linear collapse of the classifier length ledger: reading the sum-of-two-squares
-- witness through bwordLength leaves exactly `Ma1 + Mb1 = bwordLength p`, where
-- Ma1/Mb1 are the diagonal square-lengths and the off-diagonal lengths cancel.
private theorem length_collapse
    (P Ma1 Ma2 Mb1 Mb2 ta1 ta2 tb1 tb2 ya1 ya2 pa1 pa2 : Nat)
    (hTop : P + ya2 = ya1)
    (hAdd : ya1 + pa2 = pa1 + ya2)
    (hAddF : pa1 = ta1 + tb1)
    (hAddS : pa2 = ta2 + tb2)
    (hMulA : ta1 + Ma2 = Ma1 + ta2)
    (hMulB : tb1 + Mb2 = Mb1 + tb2)
    (hMa2 : Ma2 = 0) (hMb2 : Mb2 = 0) :
    Ma1 + Mb1 = P := by
  rw [hMa2, Nat.add_zero] at hMulA
  rw [hMb2, Nat.add_zero] at hMulB
  have hP : P + pa2 = pa1 := by
    apply add_right_cancel_pure (P + pa2) pa1 ya2
    rw [Nat.add_right_comm P pa2 ya2, hTop]
    exact hAdd
  rw [hAddS, hAddF, hMulA, hMulB] at hP
  have hrear : (Ma1 + ta2) + (Mb1 + tb2) = (Ma1 + Mb1) + (ta2 + tb2) := by
    rw [Nat.add_assoc Ma1 ta2 (Mb1 + tb2), ← Nat.add_assoc ta2 Mb1 tb2,
      Nat.add_comm ta2 Mb1, Nat.add_assoc Mb1 ta2 tb2,
      ← Nat.add_assoc Ma1 Mb1 (ta2 + tb2)]
  rw [hrear] at hP
  exact (add_right_cancel_pure P (Ma1 + Mb1) (ta2 + tb2) hP).symm

-- One sign-magnitude int has a zero component, so its pairMul diagonal is a
-- single square and its off-diagonal length vanishes.
private theorem diag_reduce (Ma1 Ma2 c1 c2 : Nat)
    (hd1 : Ma1 = c1 * c1 + c2 * c2) (hd2 : Ma2 = c1 * c2 + c2 * c1)
    (hz : c2 = 0 ∨ c1 = 0) : ∃ X, Ma1 = X * X ∧ Ma2 = 0 := by
  cases hz with
  | inl h =>
      exact ⟨c1, by rw [hd1, h, Nat.mul_zero, Nat.add_zero],
        by rw [hd2, h, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]⟩
  | inr h =>
      exact ⟨c2, by rw [hd1, h, Nat.zero_mul, Nat.zero_add],
        by rw [hd2, h, Nat.zero_mul, Nat.mul_zero, Nat.add_zero]⟩

private theorem classifier_length_balance {x y : BHist × BHist} :
    IntPairClassifier x y ->
      bwordLength x.1 + bwordLength y.2 =
        bwordLength y.1 + bwordLength x.2 := by
  intro classified
  have crossEq :
      BEDC.FKernel.Cont.append x.1 y.2 = BEDC.FKernel.Cont.append y.1 x.2 :=
    classified.right.right
  have lengths := congrArg bwordLength crossEq
  rw [bwordLength_append, bwordLength_append] at lengths
  exact lengths

private theorem intToPair_component_length_zero (z : Z) :
    bwordLength (intToPair z).2 = 0 ∨ bwordLength (intToPair z).1 = 0 := by
  cases z with
  | mk sign magnitude carrier =>
      cases sign
      · exact Or.inl rfl
      · exact Or.inr rfl

private theorem pairMul_diag_fst_length (z : Z) :
    bwordLength (pairMul (intToPair z) (intToPair z)).1 =
      bwordLength (intToPair z).1 * bwordLength (intToPair z).1 +
        bwordLength (intToPair z).2 * bwordLength (intToPair z).2 := by
  have carrier := intToPair_carrier z
  have step :
      bwordLength
          (BEDC.FKernel.Cont.append
            (natMulFn (intToPair z).1 (intToPair z).1)
            (natMulFn (intToPair z).2 (intToPair z).2)) =
        bwordLength (natMulFn (intToPair z).1 (intToPair z).1) +
          bwordLength (natMulFn (intToPair z).2 (intToPair z).2) :=
    bwordLength_append _ _
  rw [natMulFn_bwordLength carrier.left carrier.left,
    natMulFn_bwordLength carrier.right carrier.right] at step
  exact step

private theorem pairMul_diag_snd_length (z : Z) :
    bwordLength (pairMul (intToPair z) (intToPair z)).2 =
      bwordLength (intToPair z).1 * bwordLength (intToPair z).2 +
        bwordLength (intToPair z).2 * bwordLength (intToPair z).1 := by
  have carrier := intToPair_carrier z
  have step :
      bwordLength
          (BEDC.FKernel.Cont.append
            (natMulFn (intToPair z).1 (intToPair z).2)
            (natMulFn (intToPair z).2 (intToPair z).1)) =
        bwordLength (natMulFn (intToPair z).1 (intToPair z).2) +
          bwordLength (natMulFn (intToPair z).2 (intToPair z).1) :=
    bwordLength_append _ _
  rw [natMulFn_bwordLength carrier.left carrier.right,
    natMulFn_bwordLength carrier.right carrier.left] at step
  exact step

private theorem congruent_three_mod_four_length
    (p : BHist) (hp : UnaryHistory p)
    (pMod : NatCongruentThreeModFour p) :
    ∃ k : Nat, bwordLength p = 4 * k + 3 := by
  have unaryFour : UnaryHistory NatFour :=
    unary_e1_closed (unary_e1_closed (unary_e1_closed
      (unary_e1_closed unary_empty)))
  have fourNonempty : hsame NatFour BHist.Empty -> False :=
    fun h => BHist.noConfusion h
  cases BEDC.Derived.PadicUp.natDivRemFn_spec_pair unaryFour hp fourNonempty with
  | intro mq mqData =>
    have mqLen : bwordLength mq = 4 * bwordLength (natQuotFn NatFour p) := by
      have lenEq := BEDC.Derived.PrimeUp.NatMul_bwordLength mqData.left
      rw [show bwordLength NatFour = 4 from rfl] at lenEq
      exact lenEq
    have pLen :
        bwordLength p = bwordLength mq + bwordLength (natModFn NatFour p) := by
      have contEq :
          p = BEDC.FKernel.Cont.append mq (natModFn NatFour p) :=
        mqData.right.left.right.right
      have lenEq := congrArg bwordLength contEq
      rw [bwordLength_append] at lenEq
      exact lenEq
    have rLen : bwordLength (natModFn NatFour p) = 3 := by
      have lenEq : bwordLength (natModFn NatFour p) = bwordLength NatThree :=
        congrArg bwordLength pMod
      exact lenEq.trans (show bwordLength NatThree = 3 from rfl)
    exact ⟨bwordLength (natQuotFn NatFour p), by rw [pLen, mqLen, rLen]⟩

private theorem sum_two_squares_length_contradiction
    (p : BHist) (hp : UnaryHistory p) (a b : Z) (k : Nat)
    (pLenFour : bwordLength p = 4 * k + 3)
    (witness :
      IntPairClassifier (intToPair (intOfNat p hp))
        (intToPair (intAdd (intMul a a) (intMul b b)))) :
    False := by
  have topLen := classifier_length_balance witness
  have topFst : bwordLength (intToPair (intOfNat p hp)).1 = bwordLength p :=
    rfl
  have topSnd : bwordLength (intToPair (intOfNat p hp)).2 = 0 :=
    rfl
  rw [topFst, topSnd, Nat.add_zero] at topLen
  have addLen :=
    classifier_length_balance
      (intAdd_pair_classifier (intMul a a) (intMul b b))
  have addFst :
      bwordLength
          (pairAdd (intToPair (intMul a a)) (intToPair (intMul b b))).1 =
        bwordLength (intToPair (intMul a a)).1 +
          bwordLength (intToPair (intMul b b)).1 :=
    bwordLength_append _ _
  have addSnd :
      bwordLength
          (pairAdd (intToPair (intMul a a)) (intToPair (intMul b b))).2 =
        bwordLength (intToPair (intMul a a)).2 +
          bwordLength (intToPair (intMul b b)).2 :=
    bwordLength_append _ _
  have mulEqA : intMul a a = pairToInt (pairMul (intToPair a) (intToPair a)) :=
    rfl
  have mulEqB : intMul b b = pairToInt (pairMul (intToPair b) (intToPair b)) :=
    rfl
  have mulLenA :=
    classifier_length_balance
      (intToPair_pairToInt_classifier (pairMul (intToPair a) (intToPair a))
        (pairMul_carrier (intToPair_carrier a) (intToPair_carrier a)))
  have mulLenB :=
    classifier_length_balance
      (intToPair_pairToInt_classifier (pairMul (intToPair b) (intToPair b))
        (pairMul_carrier (intToPair_carrier b) (intToPair_carrier b)))
  rw [← mulEqA] at mulLenA
  rw [← mulEqB] at mulLenB
  have diagA1 := pairMul_diag_fst_length a
  have diagA2 := pairMul_diag_snd_length a
  have diagB1 := pairMul_diag_fst_length b
  have diagB2 := pairMul_diag_snd_length b
  cases diag_reduce _ _ _ _ diagA1 diagA2 (intToPair_component_length_zero a) with
  | intro XA hXA =>
      cases diag_reduce _ _ _ _ diagB1 diagB2 (intToPair_component_length_zero b) with
      | intro XB hXB =>
          have hColl := length_collapse _ _ _ _ _ _ _ _ _ _ _ _ _
            topLen addLen addFst addSnd mulLenA mulLenB hXA.2 hXB.2
          rw [hXA.1, hXB.1, pLenFour] at hColl
          exact natSumTwoSquares_mod_four_obstruction XA XB k hColl

theorem noSumTwoSquares_of_congruent_three_mod_four
    (p : BHist) (hp : UnaryHistory p)
    (pMod : NatCongruentThreeModFour p) :
    NoSumTwoSquares (intOfUnary p hp) := by
  intro represented
  cases congruent_three_mod_four_length p hp pMod with
  | intro k pLenFour =>
    cases represented with
    | intro a rest =>
      cases rest with
      | intro b witness =>
        exact sum_two_squares_length_contradiction p hp a b k pLenFour witness

theorem modThreeNoTwoSquaresBridge_discharge
    (p : BHist) (hp : UnaryHistory p) :
    ModThreeNoTwoSquaresBridge p hp :=
  fun _primeP pMod => noSumTwoSquares_of_congruent_three_mod_four p hp pMod

theorem rational_prime_inert_of_congruent_three_mod_four_from_factor_alternative
    {p : BHist} (hp : UnaryHistory p) :
    NatPrime p ->
      NatCongruentThreeModFour p ->
        RationalPrimeGaussianFactorAlternative (intOfUnary p hp) ->
          (GaussianUnit (gaussOfInt (intOfUnary p hp)) -> False) ->
            NormUnitReflectsGaussianUnit ->
              GaussianPrime (gaussOfInt (intOfUnary p hp)) := by
  intro primeP pMod factorAlternative rationalPrimeNonunit unitReflect
  exact rational_prime_inert_of_congruent_three_mod_four hp primeP pMod
    (modThreeNoTwoSquaresBridge_discharge p hp)
    factorAlternative rationalPrimeNonunit unitReflect

end BEDC.Derived.GaussianPrimeUp
