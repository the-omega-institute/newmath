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

end BEDC.Derived.GaussianPrimeUp
