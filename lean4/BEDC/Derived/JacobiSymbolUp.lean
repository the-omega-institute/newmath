import BEDC.Derived.JacobiUp
import BEDC.Derived.QuadraticReciprocityUp

namespace BEDC.Derived.JacobiSymbolUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.PrimeUp
open BEDC.Derived.ZModUp
open BEDC.Derived.ZModFieldUp
open BEDC.Derived.LegendreUp
open BEDC.Derived.QuadraticReciprocityUp

abbrev IntegerUp := BEDC.Algebra.Rel.IntegerUp
abbrev IntEq := BEDC.Algebra.Rel.IntEq
abbrev IntMul := BEDC.Algebra.Rel.IntMul

abbrev jacobiZero : IntegerUp :=
  legendreZero

abbrev jacobiOne : IntegerUp :=
  BEDC.Derived.JacobiUp.jacobiOne

abbrev jacobiNegOne : IntegerUp :=
  legendreNegOne

abbrev jacobiMul : IntegerUp -> IntegerUp -> IntegerUp :=
  BEDC.Derived.JacobiUp.jacobiMul

abbrev PrimeResidueAssignment :=
  BEDC.Derived.JacobiUp.PrimeResidueAssignment

abbrev LegendreAt :=
  BEDC.Derived.JacobiUp.LegendreAt

abbrev JacobiProduct :=
  BEDC.Derived.JacobiUp.JacobiProduct

abbrev OddPrimeFactorList :=
  BEDC.Derived.JacobiUp.OddPrimeFactorList

abbrev LegendrePointwiseMul :=
  BEDC.Derived.JacobiUp.LegendrePointwiseMul

/-
`JacobiSymbol a n value` 表示 `value = product_p (a / p)`，其中分母
`n` 由一个显式素因子 list 展开。本 carrier 不内建分解唯一性；使用方要么
携带自己采用的因子 list，要么另外导入已有唯一分解 surface。
-/
def JacobiSymbol (a : PrimeResidueAssignment)
    (n : BHist) (value : IntegerUp) : Prop :=
  ∃ factors : List BHist,
    PrimeFactorizationProduct factors n ∧ JacobiProduct a factors value

def JacobiOddSymbol (a : PrimeResidueAssignment)
    (n : BHist) (value : IntegerUp) : Prop :=
  ∃ factors : List BHist,
    PrimeFactorizationProduct factors n ∧ OddPrimeFactorList factors ∧
      JacobiProduct a factors value

private abbrev intRing :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

private theorem intEq_trans {x y z : IntegerUp} :
    IntEq x y -> IntEq y z -> IntEq x z := by
  intro left right
  exact intRing.trans left right

private theorem intEq_symm {x y : IntegerUp} :
    IntEq x y -> IntEq y x := by
  intro same
  exact intRing.symm same

theorem legendreSym_respects {p : BHist} (prime : NatPrime p)
    {x y : ZMod p} {s : IntegerUp} :
    zmodEq x y -> legendreSym prime x s -> legendreSym prime y s := by
  intro same symbol
  unfold legendreSym LegendreClassifies at symbol
  unfold legendreSym LegendreClassifies
  cases symbol with
  | inl zeroBranch =>
      exact Or.inl
        ⟨zmodEq_trans (zmodEq_symm same) zeroBranch.left,
          zeroBranch.right⟩
  | inr nonzeroBranch =>
      cases nonzeroBranch with
      | inl qrBranch =>
          have yQR : IsQR prime y :=
            IsQR_respects prime same qrBranch.left
          have yNonzero : zmodNonzero y := by
            exact zmodNonzero_respects same qrBranch.right.left
          exact Or.inr (Or.inl ⟨yQR, yNonzero, qrBranch.right.right⟩)
      | inr nonresidueBranch =>
          have yNonzero : zmodNonzero y := by
            exact zmodNonzero_respects same nonresidueBranch.left.left
          have yNotQR : IsQR prime y -> False := by
            intro yQR
            exact nonresidueBranch.left.right
              (IsQR_respects prime (zmodEq_symm same) yQR)
          exact Or.inr (Or.inr
            ⟨⟨yNonzero, yNotQR⟩, nonresidueBranch.right⟩)

theorem jacobiSymbol_from_factorization {a : PrimeResidueAssignment}
    {factors : List BHist} {n : BHist} {value : IntegerUp} :
    PrimeFactorizationProduct factors n ->
      JacobiProduct a factors value -> JacobiSymbol a n value := by
  intro factorProduct jacobiProduct
  exact ⟨factors, factorProduct, jacobiProduct⟩

theorem jacobiOddSymbol_from_factorization {a : PrimeResidueAssignment}
    {factors : List BHist} {n : BHist} {value : IntegerUp} :
    PrimeFactorizationProduct factors n -> OddPrimeFactorList factors ->
      JacobiProduct a factors value -> JacobiOddSymbol a n value := by
  intro factorProduct oddFactors jacobiProduct
  exact ⟨factors, factorProduct, oddFactors, jacobiProduct⟩

theorem jacobiSymbol_prime_consistent {a : PrimeResidueAssignment}
    {p : BHist} {value : IntegerUp} (prime : NatPrime p) :
    legendreSym prime (a p) value -> JacobiSymbol a p value := by
  intro legendreValue
  exact jacobiSymbol_from_factorization
    (BEDC.Derived.JacobiUp.primeFactorizationProduct_single prime)
    (BEDC.Derived.JacobiUp.jacobiProduct_prime_consistent
      prime legendreValue)

theorem jacobiSymbol_zero_mod_prime {a : PrimeResidueAssignment}
    {p : BHist} (prime : NatPrime p) :
    zmodEq (a p)
      (zmodZero p prime.left (NatPrime_empty_absurd prime)) ->
        JacobiSymbol a p jacobiZero := by
  intro sameZero
  exact jacobiSymbol_prime_consistent prime
    (legendreSym_respects prime (zmodEq_symm sameZero)
      (legendreSym_zero prime))

theorem jacobiSymbol_one_mod_prime {a : PrimeResidueAssignment}
    {p : BHist} (prime : NatPrime p) :
    zmodEq (a p)
      (zmodOne p prime.left (NatPrime_empty_absurd prime)) ->
        JacobiSymbol a p jacobiOne := by
  intro sameOne
  exact jacobiSymbol_prime_consistent prime
    (legendreSym_respects prime (zmodEq_symm sameOne)
      (legendreSym_one prime))

theorem jacobiSymbol_denominator_mul {a : PrimeResidueAssignment}
    {m n mn : BHist} {leftValue rightValue : IntegerUp} :
    JacobiSymbol a m leftValue -> JacobiSymbol a n rightValue ->
      NatMul m n mn ->
        JacobiSymbol a mn (jacobiMul leftValue rightValue) := by
  intro leftSymbol rightSymbol productMN
  cases leftSymbol with
  | intro leftFactors leftData =>
      cases rightSymbol with
      | intro rightFactors rightData =>
          exact jacobiSymbol_from_factorization
            (BEDC.Derived.JacobiUp.primeFactorizationProduct_append
              leftData.left rightData.left productMN)
            (BEDC.Derived.JacobiUp.jacobiProduct_append
              leftData.right rightData.right)

theorem jacobiSymbol_numerator_mul_on_factorization
    {a b ab : PrimeResidueAssignment}
    {factors : List BHist} {n : BHist} {va vb : IntegerUp} :
    PrimeFactorizationProduct factors n ->
      LegendrePointwiseMul a b ab factors ->
        JacobiProduct a factors va -> JacobiProduct b factors vb ->
          JacobiSymbol ab n (jacobiMul va vb) := by
  intro factorProduct pointwise leftProduct rightProduct
  exact jacobiSymbol_from_factorization factorProduct
    (BEDC.Derived.JacobiUp.jacobiProduct_numerator_mul
      pointwise leftProduct rightProduct)

theorem jacobiSymbol_numerator_mul_displayed
    {a b ab : PrimeResidueAssignment}
    {n : BHist} {va vb : IntegerUp} :
    (∃ factors : List BHist,
      PrimeFactorizationProduct factors n ∧
        LegendrePointwiseMul a b ab factors ∧
          JacobiProduct a factors va ∧ JacobiProduct b factors vb) ->
      JacobiSymbol ab n (jacobiMul va vb) := by
  intro displayed
  cases displayed with
  | intro factors data =>
      exact jacobiSymbol_numerator_mul_on_factorization data.left
        data.right.left data.right.right.left data.right.right.right

theorem jacobiProduct_denominator_mul {a : PrimeResidueAssignment}
    {left right : List BHist} {leftValue rightValue value : IntegerUp} :
    JacobiProduct a left leftValue -> JacobiProduct a right rightValue ->
      IntEq value (jacobiMul leftValue rightValue) ->
        JacobiProduct a (left ++ right) value := by
  intro leftProduct rightProduct valueEq
  exact BEDC.Derived.JacobiUp.jacobiProduct_denominator_mul
    leftProduct rightProduct valueEq

def jacobiQRSignMatches (s : IntegerUp) (sign : QRSign) : Prop :=
  (sign = QRSign.pos ∧ IntEq s jacobiOne) ∨
    (sign = QRSign.neg ∧ IntEq s jacobiNegOne)

theorem jacobi_prime_reciprocity_from_gauss_eisenstein
    {pHist qHist : BHist} {p q : Nat} {pq qp : QRSign}
    {a b : PrimeResidueAssignment} {sp sq : IntegerUp} :
    p = BEDC.FKernel.ExternalBinary.bwordLength pHist ->
      q = BEDC.FKernel.ExternalBinary.bwordLength qHist ->
        JacobiSymbol a pHist sp -> JacobiSymbol b qHist sq ->
          jacobiQRSignMatches sp pq -> jacobiQRSignMatches sq qp ->
            GaussLemmaShapeEq p q pq -> GaussLemmaShapeEq q p qp ->
              NegCountParityEqFloorSumEq p q ->
                NegCountParityEqFloorSumEq q p ->
                  EisensteinFloorSumEq p q ->
                    p = BEDC.FKernel.ExternalBinary.bwordLength pHist ∧
                      q = BEDC.FKernel.ExternalBinary.bwordLength qHist ∧
                        JacobiSymbol a pHist sp ∧ JacobiSymbol b qHist sq ∧
                          jacobiQRSignMatches sp pq ∧
                            jacobiQRSignMatches sq qp ∧
                              QRFormulaEq p q pq qp := by
  intro pLength qLength leftSymbol rightSymbol leftSign rightSign
  intro gaussPQ gaussQP parityPQ parityQP eisenstein
  exact ⟨pLength, qLength, leftSymbol, rightSymbol, leftSign, rightSign,
    quadraticReciprocityFormula_from_gauss_eisenstein
      gaussPQ gaussQP parityPQ parityQP eisenstein⟩

theorem jacobiSymbol_intEq_congr {a : PrimeResidueAssignment}
    {n : BHist} {x y : IntegerUp} :
    IntEq x y -> JacobiSymbol a n y -> JacobiSymbol a n x := by
  intro same symbol
  cases symbol with
  | intro factors data =>
      exact jacobiSymbol_from_factorization data.left
        (BEDC.Derived.JacobiUp.JacobiProduct_congr same data.right)

theorem jacobiSymbol_intEq_symm_congr {a : PrimeResidueAssignment}
    {n : BHist} {x y : IntegerUp} :
    IntEq y x -> JacobiSymbol a n y -> JacobiSymbol a n x := by
  intro same symbol
  exact jacobiSymbol_intEq_congr (intEq_symm same) symbol

theorem jacobiSymbol_intEq_trans_value {a : PrimeResidueAssignment}
    {n : BHist} {x y z : IntegerUp} :
    IntEq x y -> IntEq y z -> JacobiSymbol a n z -> JacobiSymbol a n x := by
  intro left right symbol
  exact jacobiSymbol_intEq_congr (intEq_trans left right) symbol

end BEDC.Derived.JacobiSymbolUp
