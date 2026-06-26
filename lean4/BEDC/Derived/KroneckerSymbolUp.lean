import BEDC.Derived.JacobiUp
import BEDC.Derived.IntUp.CommRing
import BEDC.Algebra.Rel.IntegerUp

namespace BEDC.Derived.KroneckerSymbolUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.JacobiUp

abbrev IntegerUp := BEDC.Algebra.Rel.IntegerUp
abbrev IntEq := BEDC.Algebra.Rel.IntEq
abbrev IntMul := BEDC.Algebra.Rel.IntMul

abbrev NatOne : BHist := BHist.e1 BHist.Empty
abbrev NatTwo : BHist := BHist.e1 NatOne
abbrev NatThree : BHist := BHist.e1 NatTwo
abbrev NatFour : BHist := BHist.e1 NatThree
abbrev NatFive : BHist := BHist.e1 NatFour
abbrev NatSix : BHist := BHist.e1 NatFive
abbrev NatSeven : BHist := BHist.e1 NatSix
abbrev NatEight : BHist := BHist.e1 NatSeven

def kroneckerZero : IntegerUp :=
  BEDC.Algebra.Rel.intZero

def kroneckerOne : IntegerUp :=
  BEDC.Algebra.Rel.intOne

def kroneckerNegOne : IntegerUp :=
  BEDC.Algebra.Rel.IntNeg BEDC.Algebra.Rel.intOne

def kroneckerTwoDenominator : IntegerUp :=
  BEDC.Derived.RationalUp.intOfNat NatTwo
    (unary_e1_closed (unary_e1_closed unary_empty))

private abbrev intRing :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

private theorem intEq_refl (x : IntegerUp) : IntEq x x :=
  intRing.refl x

private theorem intEq_symm {x y : IntegerUp} :
    IntEq x y -> IntEq y x := by
  intro same
  exact intRing.symm same

private theorem intEq_trans {x y z : IntegerUp} :
    IntEq x y -> IntEq y z -> IntEq x z := by
  intro left right
  exact intRing.trans left right

private theorem intMul_respects {a a' b b' : IntegerUp} :
    IntEq a a' -> IntEq b b' -> IntEq (IntMul a b) (IntMul a' b') := by
  intro left right
  exact intRing.mul_congr left right

private theorem intMul_assoc (a b c : IntegerUp) :
    IntEq (IntMul (IntMul a b) c) (IntMul a (IntMul b c)) :=
  intRing.mul_assoc a b c

private theorem intMul_one (a : IntegerUp) :
    IntEq (IntMul a kroneckerOne) a :=
  intRing.mul_one a

private theorem intMul_one_left (a : IntegerUp) :
    IntEq (IntMul kroneckerOne a) a :=
  intRing.one_mul a

private theorem intOfNat_carrier_congr (n : BHist)
    (left right : UnaryHistory n) :
    IntEq (BEDC.Derived.RationalUp.intOfNat n left)
      (BEDC.Derived.RationalUp.intOfNat n right) := by
  exact intRing.refl (BEDC.Derived.RationalUp.intOfNat n left)

private theorem unary_hsame_of_length {h k : BHist} :
    UnaryHistory h -> UnaryHistory k -> bwordLength h = bwordLength k ->
      hsame h k := by
  intro hUnary kUnary lengthEq
  exact (NatUp_unary_standard_bridge.right.right.right.left
    hUnary kUnary).mpr lengthEq

private theorem intOfNat_hsame_congr {m n : BHist}
    (mUnary : UnaryHistory m) (nUnary : UnaryHistory n) :
    hsame m n ->
      IntEq (BEDC.Derived.RationalUp.intOfNat m mUnary)
        (BEDC.Derived.RationalUp.intOfNat n nUnary) := by
  intro same
  change BEDC.Derived.RationalUp.IntEq
    (BEDC.Derived.RationalUp.intOfNat m mUnary)
    (BEDC.Derived.RationalUp.intOfNat n nUnary)
  unfold BEDC.Derived.RationalUp.IntEq
  unfold BEDC.Derived.RationalUp.intOfNat
  apply BEDC.Derived.RationalUp.IntPairClassifier_of_length_eq
  · exact ⟨mUnary, unary_empty⟩
  · exact ⟨nUnary, unary_empty⟩
  · have sameLength : bwordLength m = bwordLength n :=
      congrArg bwordLength same
    change bwordLength m + bwordLength BHist.Empty =
      bwordLength n + bwordLength BHist.Empty
    rw [NatUp_unary_standard_bridge.left]
    rw [Nat.add_zero]
    rw [Nat.add_zero]
    exact sameLength

structure KroneckerNumerator where
  integer : IntegerUp
  oddResidue : PrimeResidueAssignment

inductive KroneckerDenominatorFactor where
  | minusOne
  | two
  | oddPrime (p : BHist)

def intModEightResidue (a : IntegerUp) : BHist :=
  match a.sign with
  | BMark.b0 => natModFn NatEight a.magnitude
  | BMark.b1 => natComplementMod NatEight a.magnitude

inductive ResidueEight where
  | r0
  | r1
  | r2
  | r3
  | r4
  | r5
  | r6
  | r7

def ResidueEight.next : ResidueEight -> ResidueEight
  | ResidueEight.r0 => ResidueEight.r1
  | ResidueEight.r1 => ResidueEight.r2
  | ResidueEight.r2 => ResidueEight.r3
  | ResidueEight.r3 => ResidueEight.r4
  | ResidueEight.r4 => ResidueEight.r5
  | ResidueEight.r5 => ResidueEight.r6
  | ResidueEight.r6 => ResidueEight.r7
  | ResidueEight.r7 => ResidueEight.r0

def residueEightOfUnary : BHist -> ResidueEight
  | BHist.Empty => ResidueEight.r0
  | BHist.e0 h => residueEightOfUnary h
  | BHist.e1 h => ResidueEight.next (residueEightOfUnary h)

def KroneckerSignValue (code : ResidueEight) (value : IntegerUp) : Prop :=
  match code with
  | ResidueEight.r0 => IntEq value kroneckerZero
  | ResidueEight.r1 => IntEq value kroneckerOne
  | ResidueEight.r2 => IntEq value kroneckerZero
  | ResidueEight.r3 => IntEq value kroneckerNegOne
  | ResidueEight.r4 => IntEq value kroneckerZero
  | ResidueEight.r5 => IntEq value kroneckerNegOne
  | ResidueEight.r6 => IntEq value kroneckerZero
  | ResidueEight.r7 => IntEq value kroneckerOne

def KroneckerTwoValue (a : IntegerUp) (value : IntegerUp) : Prop :=
  KroneckerSignValue (residueEightOfUnary (intModEightResidue a)) value

def KroneckerMinusOneValue (a : IntegerUp) (value : IntegerUp) : Prop :=
  (a.sign = BMark.b1 ∧ (hsame a.magnitude BHist.Empty -> False) ∧
      IntEq value kroneckerNegOne) ∨
    ((a.sign = BMark.b0 ∨ hsame a.magnitude BHist.Empty) ∧
      IntEq value kroneckerOne)

def KroneckerZeroDenominatorValue (a : IntegerUp) (value : IntegerUp) : Prop :=
  (hsame a.magnitude NatOne ∧ IntEq value kroneckerOne) ∨
    ((hsame a.magnitude NatOne -> False) ∧ IntEq value kroneckerZero)

def KroneckerFactorValue
    (a : KroneckerNumerator) :
    KroneckerDenominatorFactor -> IntegerUp -> Prop
  | KroneckerDenominatorFactor.minusOne, value =>
      KroneckerMinusOneValue a.integer value
  | KroneckerDenominatorFactor.two, value =>
      KroneckerTwoValue a.integer value
  | KroneckerDenominatorFactor.oddPrime p, value =>
      LegendreAt a.oddResidue p value

def KroneckerFactorDenominator :
    KroneckerDenominatorFactor -> IntegerUp -> Prop
  | KroneckerDenominatorFactor.minusOne, value =>
      IntEq value kroneckerNegOne
  | KroneckerDenominatorFactor.two, value =>
      IntEq value kroneckerTwoDenominator
  | KroneckerDenominatorFactor.oddPrime p, value =>
      ∃ prime : NatPrime p,
        IntEq value (BEDC.Derived.RationalUp.intOfNat p prime.left)

def KroneckerProduct (a : KroneckerNumerator) :
    List KroneckerDenominatorFactor -> IntegerUp -> Prop
  | [], value => IntEq value kroneckerOne
  | factor :: factors, value =>
      ∃ head tail : IntegerUp,
        KroneckerFactorValue a factor head ∧
          KroneckerProduct a factors tail ∧ IntEq value (IntMul head tail)

def KroneckerDenominatorProduct :
    List KroneckerDenominatorFactor -> IntegerUp -> Prop
  | [], value => IntEq value kroneckerOne
  | factor :: factors, value =>
      ∃ head tail : IntegerUp,
        KroneckerFactorDenominator factor head ∧
          KroneckerDenominatorProduct factors tail ∧
            IntEq value (IntMul head tail)

def KroneckerSymbol
    (a : KroneckerNumerator) (denominator value : IntegerUp) : Prop :=
  (IntEq denominator kroneckerZero ∧
      KroneckerZeroDenominatorValue a.integer value) ∨
    ∃ factors : List KroneckerDenominatorFactor,
      KroneckerDenominatorProduct factors denominator ∧
        KroneckerProduct a factors value

def oddPrimeFactors : List BHist -> List KroneckerDenominatorFactor
  | [] => []
  | p :: ps => KroneckerDenominatorFactor.oddPrime p :: oddPrimeFactors ps

theorem kroneckerTwo_residue_zero {a : IntegerUp} :
    residueEightOfUnary (intModEightResidue a) = ResidueEight.r0 ->
      KroneckerTwoValue a kroneckerZero := by
  intro same
  unfold KroneckerTwoValue
  rw [same]
  exact intEq_refl kroneckerZero

theorem kroneckerTwo_residue_one {a : IntegerUp} :
    residueEightOfUnary (intModEightResidue a) = ResidueEight.r1 ->
      KroneckerTwoValue a kroneckerOne := by
  intro same
  unfold KroneckerTwoValue
  rw [same]
  exact intEq_refl kroneckerOne

theorem kroneckerTwo_residue_two {a : IntegerUp} :
    residueEightOfUnary (intModEightResidue a) = ResidueEight.r2 ->
      KroneckerTwoValue a kroneckerZero := by
  intro same
  unfold KroneckerTwoValue
  rw [same]
  exact intEq_refl kroneckerZero

theorem kroneckerTwo_residue_three {a : IntegerUp} :
    residueEightOfUnary (intModEightResidue a) = ResidueEight.r3 ->
      KroneckerTwoValue a kroneckerNegOne := by
  intro same
  unfold KroneckerTwoValue
  rw [same]
  exact intEq_refl kroneckerNegOne

theorem kroneckerTwo_residue_four {a : IntegerUp} :
    residueEightOfUnary (intModEightResidue a) = ResidueEight.r4 ->
      KroneckerTwoValue a kroneckerZero := by
  intro same
  unfold KroneckerTwoValue
  rw [same]
  exact intEq_refl kroneckerZero

theorem kroneckerTwo_residue_five {a : IntegerUp} :
    residueEightOfUnary (intModEightResidue a) = ResidueEight.r5 ->
      KroneckerTwoValue a kroneckerNegOne := by
  intro same
  unfold KroneckerTwoValue
  rw [same]
  exact intEq_refl kroneckerNegOne

theorem kroneckerTwo_residue_six {a : IntegerUp} :
    residueEightOfUnary (intModEightResidue a) = ResidueEight.r6 ->
      KroneckerTwoValue a kroneckerZero := by
  intro same
  unfold KroneckerTwoValue
  rw [same]
  exact intEq_refl kroneckerZero

theorem kroneckerTwo_residue_seven {a : IntegerUp} :
    residueEightOfUnary (intModEightResidue a) = ResidueEight.r7 ->
      KroneckerTwoValue a kroneckerOne := by
  intro same
  unfold KroneckerTwoValue
  rw [same]
  exact intEq_refl kroneckerOne

theorem kroneckerMinusOne_negative {a : IntegerUp} :
    a.sign = BMark.b1 -> (hsame a.magnitude BHist.Empty -> False) ->
      KroneckerMinusOneValue a kroneckerNegOne := by
  intro signEq nonempty
  exact Or.inl ⟨signEq, nonempty, intEq_refl kroneckerNegOne⟩

theorem kroneckerMinusOne_nonnegative {a : IntegerUp} :
    (a.sign = BMark.b0 ∨ hsame a.magnitude BHist.Empty) ->
      KroneckerMinusOneValue a kroneckerOne := by
  intro nonnegative
  exact Or.inr ⟨nonnegative, intEq_refl kroneckerOne⟩

theorem kroneckerZeroDenominator_unit {a : IntegerUp} :
    hsame a.magnitude NatOne ->
      KroneckerZeroDenominatorValue a kroneckerOne := by
  intro unitMagnitude
  exact Or.inl ⟨unitMagnitude, intEq_refl kroneckerOne⟩

theorem kroneckerZeroDenominator_nonunit {a : IntegerUp} :
    (hsame a.magnitude NatOne -> False) ->
      KroneckerZeroDenominatorValue a kroneckerZero := by
  intro nonunit
  exact Or.inr ⟨nonunit, intEq_refl kroneckerZero⟩

theorem KroneckerProduct_congr {a : KroneckerNumerator}
    {factors : List KroneckerDenominatorFactor} {x y : IntegerUp} :
    IntEq x y -> KroneckerProduct a factors y ->
      KroneckerProduct a factors x := by
  intro same product
  induction factors generalizing x y with
  | nil =>
      change IntEq y kroneckerOne at product
      change IntEq x kroneckerOne
      exact intEq_trans same product
  | cons factor factors ih =>
      cases product with
      | intro head headRest =>
          cases headRest with
          | intro tail data =>
              exact ⟨head, tail, data.left, data.right.left,
                intEq_trans same data.right.right⟩

theorem KroneckerDenominatorProduct_congr
    {factors : List KroneckerDenominatorFactor} {x y : IntegerUp} :
    IntEq x y -> KroneckerDenominatorProduct factors y ->
      KroneckerDenominatorProduct factors x := by
  intro same product
  induction factors generalizing x y with
  | nil =>
      change IntEq y kroneckerOne at product
      change IntEq x kroneckerOne
      exact intEq_trans same product
  | cons factor factors ih =>
      cases product with
      | intro head headRest =>
          cases headRest with
          | intro tail data =>
              exact ⟨head, tail, data.left, data.right.left,
                intEq_trans same data.right.right⟩

theorem KroneckerProduct_cons {a : KroneckerNumerator}
    {factor : KroneckerDenominatorFactor}
    {factors : List KroneckerDenominatorFactor}
    {head tail value : IntegerUp} :
    KroneckerFactorValue a factor head ->
      KroneckerProduct a factors tail ->
        IntEq value (IntMul head tail) ->
          KroneckerProduct a (factor :: factors) value := by
  intro headValue tailProduct valueEq
  exact ⟨head, tail, headValue, tailProduct, valueEq⟩

theorem KroneckerDenominatorProduct_cons
    {factor : KroneckerDenominatorFactor}
    {factors : List KroneckerDenominatorFactor}
    {head tail value : IntegerUp} :
    KroneckerFactorDenominator factor head ->
      KroneckerDenominatorProduct factors tail ->
        IntEq value (IntMul head tail) ->
          KroneckerDenominatorProduct (factor :: factors) value := by
  intro headValue tailProduct valueEq
  exact ⟨head, tail, headValue, tailProduct, valueEq⟩

theorem kroneckerProduct_append {a : KroneckerNumerator}
    {left right : List KroneckerDenominatorFactor}
    {leftValue rightValue : IntegerUp} :
    KroneckerProduct a left leftValue ->
      KroneckerProduct a right rightValue ->
        KroneckerProduct a (left ++ right) (IntMul leftValue rightValue) := by
  intro leftProduct rightProduct
  induction left generalizing leftValue with
  | nil =>
      change IntEq leftValue kroneckerOne at leftProduct
      change KroneckerProduct a right (IntMul leftValue rightValue)
      exact KroneckerProduct_congr
        (intEq_trans
          (intMul_respects leftProduct (intEq_refl rightValue))
          (intMul_one_left rightValue))
        rightProduct
  | cons factor factors ih =>
      cases leftProduct with
      | intro head headRest =>
          cases headRest with
          | intro tail rest =>
              have tailApp :
                  KroneckerProduct a (factors ++ right)
                    (IntMul tail rightValue) :=
                ih rest.right.left
              refine KroneckerProduct_cons rest.left tailApp ?_
              exact intEq_trans
                (intMul_respects rest.right.right (intEq_refl rightValue))
                (intMul_assoc head tail rightValue)

theorem kroneckerDenominatorProduct_append
    {left right : List KroneckerDenominatorFactor}
    {leftValue rightValue : IntegerUp} :
    KroneckerDenominatorProduct left leftValue ->
      KroneckerDenominatorProduct right rightValue ->
        KroneckerDenominatorProduct (left ++ right)
          (IntMul leftValue rightValue) := by
  intro leftProduct rightProduct
  induction left generalizing leftValue with
  | nil =>
      change IntEq leftValue kroneckerOne at leftProduct
      change KroneckerDenominatorProduct right (IntMul leftValue rightValue)
      exact KroneckerDenominatorProduct_congr
        (intEq_trans
          (intMul_respects leftProduct (intEq_refl rightValue))
          (intMul_one_left rightValue))
        rightProduct
  | cons factor factors ih =>
      cases leftProduct with
      | intro head headRest =>
          cases headRest with
          | intro tail rest =>
              have tailApp :
                  KroneckerDenominatorProduct (factors ++ right)
                    (IntMul tail rightValue) :=
                ih rest.right.left
              refine KroneckerDenominatorProduct_cons rest.left tailApp ?_
              exact intEq_trans
                (intMul_respects rest.right.right (intEq_refl rightValue))
                (intMul_assoc head tail rightValue)

theorem kroneckerSymbol_zero {a : KroneckerNumerator}
    {value : IntegerUp} :
    KroneckerZeroDenominatorValue a.integer value ->
      KroneckerSymbol a kroneckerZero value := by
  intro zeroValue
  exact Or.inl ⟨intEq_refl kroneckerZero, zeroValue⟩

theorem kroneckerSymbol_one {a : KroneckerNumerator} :
    KroneckerSymbol a kroneckerOne kroneckerOne := by
  exact Or.inr ⟨[], intEq_refl kroneckerOne, intEq_refl kroneckerOne⟩

theorem kroneckerSymbol_minusOne {a : KroneckerNumerator}
    {value : IntegerUp} :
    KroneckerMinusOneValue a.integer value ->
      KroneckerSymbol a kroneckerNegOne value := by
  intro minusValue
  exact Or.inr
    ⟨[KroneckerDenominatorFactor.minusOne],
      ⟨kroneckerNegOne, kroneckerOne, intEq_refl kroneckerNegOne,
        intEq_refl kroneckerOne,
        intEq_symm (intMul_one kroneckerNegOne)⟩,
      ⟨value, kroneckerOne, minusValue, intEq_refl kroneckerOne,
        intEq_symm (intMul_one value)⟩⟩

theorem kroneckerSymbol_two {a : KroneckerNumerator}
    {value : IntegerUp} :
    KroneckerTwoValue a.integer value ->
      KroneckerSymbol a kroneckerTwoDenominator value := by
  intro twoValue
  exact Or.inr
    ⟨[KroneckerDenominatorFactor.two],
      ⟨kroneckerTwoDenominator, kroneckerOne,
        intEq_refl kroneckerTwoDenominator,
        intEq_refl kroneckerOne,
        intEq_symm (intMul_one kroneckerTwoDenominator)⟩,
      ⟨value, kroneckerOne, twoValue, intEq_refl kroneckerOne,
        intEq_symm (intMul_one value)⟩⟩

theorem kroneckerSymbol_denominator_mul {a : KroneckerNumerator}
    {left right : List KroneckerDenominatorFactor}
    {leftDen rightDen leftValue rightValue : IntegerUp} :
    KroneckerDenominatorProduct left leftDen ->
      KroneckerDenominatorProduct right rightDen ->
        KroneckerProduct a left leftValue ->
          KroneckerProduct a right rightValue ->
            KroneckerSymbol a (IntMul leftDen rightDen)
              (IntMul leftValue rightValue) := by
  intro leftDenProduct rightDenProduct leftProduct rightProduct
  exact Or.inr
    ⟨left ++ right,
      kroneckerDenominatorProduct_append leftDenProduct rightDenProduct,
      kroneckerProduct_append leftProduct rightProduct⟩

theorem kroneckerProduct_oddPrimeFactors_jacobiProduct
    {a : KroneckerNumerator} {factors : List BHist}
    {value : IntegerUp} :
    JacobiProduct a.oddResidue factors value ->
      KroneckerProduct a (oddPrimeFactors factors) value := by
  intro jacobiProduct
  induction factors generalizing value with
  | nil =>
      change IntEq value kroneckerOne at jacobiProduct
      change KroneckerProduct a [] value
      exact jacobiProduct
  | cons p ps ih =>
      cases jacobiProduct with
      | intro head headRest =>
          cases headRest with
          | intro tail data =>
              have tailProduct : KroneckerProduct a (oddPrimeFactors ps) tail :=
                ih data.right.left
              exact KroneckerProduct_cons data.left tailProduct data.right.right

theorem kroneckerDenominatorProduct_oddPrimeFactors
    {factors : List BHist} {n : BHist}
    (product : PrimeFactorizationProduct factors n) :
      KroneckerDenominatorProduct (oddPrimeFactors factors)
        (BEDC.Derived.RationalUp.intOfNat n
          (PrimeFactorizationProduct_result_unary product)) := by
  induction factors generalizing n with
  | nil =>
      have nUnary : UnaryHistory n :=
        unary_transport (unary_e1_closed unary_empty) (hsame_symm product)
      change hsame n NatOne at product
      change IntEq
        (BEDC.Derived.RationalUp.intOfNat n
          nUnary) kroneckerOne
      unfold kroneckerOne BEDC.Algebra.Rel.intOne
      unfold BEDC.Derived.RationalUp.intOne
      exact intOfNat_hsame_congr nUnary
        (unary_e1_closed unary_empty) product
  | cons p ps ih =>
      cases product with
      | intro pPrime tailData =>
          cases tailData with
          | intro tailProduct rest =>
              have tailDen :
                  KroneckerDenominatorProduct (oddPrimeFactors ps)
                  (BEDC.Derived.RationalUp.intOfNat tailProduct
                      (PrimeFactorizationProduct_result_unary rest.left)) :=
                ih rest.left
              have computedDen :
                  IntEq
                    (IntMul
                      (BEDC.Derived.RationalUp.intOfNat p pPrime.left)
                      (BEDC.Derived.RationalUp.intOfNat tailProduct
                        (PrimeFactorizationProduct_result_unary rest.left)))
                    (BEDC.Derived.RationalUp.intOfNat (natMulFn p tailProduct)
                      (natMulFn_unary pPrime.left
                        (PrimeFactorizationProduct_result_unary rest.left))) :=
                BEDC.Derived.RationalUp.intMul_same_sign_nat
                  BMark.b0 p tailProduct pPrime.left
                  (PrimeFactorizationProduct_result_unary rest.left)
              have sameProduct :
                  hsame n (natMulFn p tailProduct) :=
                NatMul_functional pPrime.left rest.right
                  (natMulFn_rel pPrime.left
                    (PrimeFactorizationProduct_result_unary rest.left))
              have targetDen :
                  IntEq
                    (BEDC.Derived.RationalUp.intOfNat (natMulFn p tailProduct)
                      (natMulFn_unary pPrime.left
                        (PrimeFactorizationProduct_result_unary rest.left)))
                    (BEDC.Derived.RationalUp.intOfNat n
                      (NatMul_result_unary pPrime.left rest.right)) := by
                exact intOfNat_hsame_congr
                  (natMulFn_unary pPrime.left
                    (PrimeFactorizationProduct_result_unary rest.left))
                  (NatMul_result_unary pPrime.left rest.right)
                  (hsame_symm sameProduct)
              have carrierDen :
                  IntEq
                    (BEDC.Derived.RationalUp.intOfNat n
                      (NatMul_result_unary pPrime.left rest.right))
                    (BEDC.Derived.RationalUp.intOfNat n
                      (PrimeFactorizationProduct_result_unary
                        (show PrimeFactorizationProduct (p :: ps) n from
                          And.intro pPrime
                            (Exists.intro tailProduct rest)))) :=
                intOfNat_carrier_congr n _ _
              refine KroneckerDenominatorProduct_cons
                ⟨pPrime,
                  intEq_refl
                    (BEDC.Derived.RationalUp.intOfNat p pPrime.left)⟩
                tailDen ?_
              exact intEq_symm
                (intEq_trans computedDen
                  (intEq_trans targetDen carrierDen))

theorem kroneckerProduct_jacobiSymbol_consistent
    {a : KroneckerNumerator} {n : BHist} {value : IntegerUp} :
    JacobiSymbol a.oddResidue n value ->
      ∃ factors : List BHist,
        PrimeFactorizationProduct factors n ∧
          KroneckerProduct a (oddPrimeFactors factors) value := by
  intro jacobiSymbol
  cases jacobiSymbol with
  | intro factors data =>
      exact ⟨factors, data.left,
        kroneckerProduct_oddPrimeFactors_jacobiProduct data.right⟩

theorem kroneckerSymbol_jacobiSymbol_consistent
    {a : KroneckerNumerator} {n : BHist} (nUnary : UnaryHistory n)
    {value : IntegerUp} :
    JacobiSymbol a.oddResidue n value ->
      KroneckerSymbol a
        (BEDC.Derived.RationalUp.intOfNat n nUnary) value := by
  intro jacobiSymbol
  cases jacobiSymbol with
  | intro factors data =>
      have sameDen :
          IntEq
            (BEDC.Derived.RationalUp.intOfNat n nUnary)
            (BEDC.Derived.RationalUp.intOfNat n
              (PrimeFactorizationProduct_result_unary data.left)) :=
        intOfNat_carrier_congr n nUnary
          (PrimeFactorizationProduct_result_unary data.left)
      exact Or.inr
        ⟨oddPrimeFactors factors,
          KroneckerDenominatorProduct_congr sameDen
            (kroneckerDenominatorProduct_oddPrimeFactors data.left),
          kroneckerProduct_oddPrimeFactors_jacobiProduct data.right⟩

theorem kroneckerProduct_prime_consistent
    {a : KroneckerNumerator} {p : BHist} {value : IntegerUp}
    (prime : NatPrime p) :
    BEDC.Derived.LegendreUp.legendreSym prime (a.oddResidue p) value ->
      KroneckerProduct a [KroneckerDenominatorFactor.oddPrime p] value := by
  intro legendre
  exact KroneckerProduct_cons
    ⟨prime, legendre⟩
    (intEq_refl kroneckerOne)
    (intEq_symm (intMul_one value))

theorem kroneckerSymbol_prime_consistent
    {a : KroneckerNumerator} {p : BHist} {value : IntegerUp}
    (prime : NatPrime p) :
    BEDC.Derived.LegendreUp.legendreSym prime (a.oddResidue p) value ->
      KroneckerSymbol a
        (BEDC.Derived.RationalUp.intOfNat p prime.left) value := by
  intro legendre
  exact Or.inr
    ⟨[KroneckerDenominatorFactor.oddPrime p],
      ⟨BEDC.Derived.RationalUp.intOfNat p prime.left,
        kroneckerOne,
        ⟨prime, intEq_refl (BEDC.Derived.RationalUp.intOfNat p prime.left)⟩,
        intEq_refl kroneckerOne,
        intEq_symm
          (intMul_one (BEDC.Derived.RationalUp.intOfNat p prime.left))⟩,
      kroneckerProduct_prime_consistent prime legendre⟩

end BEDC.Derived.KroneckerSymbolUp
