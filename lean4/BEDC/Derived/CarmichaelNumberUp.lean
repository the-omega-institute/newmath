import BEDC.Derived.CarmichaelUp

namespace BEDC.Derived.CarmichaelNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ArithmeticFnUp
open BEDC.Derived.CarmichaelUp
open BEDC.Derived.IntUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.ZModUp

/-!
Carmichael 数导出面只登记已经由 `CarmichaelUp` 证明的闭合链。
Korselt 到全剩余条件的方向仍缺少中国剩余分解和幂提升桥，本文件不伪造该闭合。
-/

abbrev NatTwo : BHist := CarmichaelUp.NatTwo
abbrev NatThree : BHist := CarmichaelUp.NatThree
abbrev NatEleven : BHist := CarmichaelUp.NatEleven
abbrev NatSeventeen : BHist := CarmichaelUp.NatSeventeen
abbrev NatFiveHundredSixtyOne : BHist := CarmichaelUp.NatFiveHundredSixtyOne

def CarmichaelNumber (n : BHist) : Prop :=
  CarmichaelUp.CarmichaelNumber n

def CarmichaelResidueCondition
    (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) : Prop :=
  CarmichaelUp.CarmichaelResidueCondition n nUnary nNonempty

def CompositeNumber (n : BHist) : Prop :=
  CarmichaelUp.NatComposite n

def KorseltCriterion (n : BHist) (factors : List BHist) : Prop :=
  CarmichaelUp.CarmichaelViaKorselt n factors

def KorseltFactorLedger (n : BHist) (factors : List BHist) : Prop :=
  PrimeFactorization n factors ∧ listSquarefree factors ∧
    ∀ p : BHist, p ∈ factors ->
      CarmichaelUp.PrimeFactorDividesPredecessor p n

theorem korseltCriterion_iff_factor_ledger {n : BHist} {factors : List BHist} :
    KorseltCriterion n factors ↔
      CompositeNumber n ∧ KorseltFactorLedger n factors := by
  constructor
  · intro cert
    exact ⟨cert.left, cert.right.left, cert.right.right.left, cert.right.right.right⟩
  · intro data
    exact ⟨data.left, data.right.left, data.right.right.left, data.right.right.right⟩

theorem korseltCriterion_components {n : BHist} {factors : List BHist} :
    KorseltCriterion n factors ->
      CompositeNumber n ∧ PrimeFactorization n factors ∧ listSquarefree factors ∧
        ∀ p : BHist, p ∈ factors ->
          CarmichaelUp.PrimeFactorDividesPredecessor p n := by
  intro cert
  exact CarmichaelUp.carmichaelViaKorselt_iff_components.mp cert

theorem korseltCriterion_factor_ledger {n : BHist} {factors : List BHist} :
    KorseltCriterion n factors -> KorseltFactorLedger n factors := by
  intro cert
  exact ⟨cert.right.left, cert.right.right.left, cert.right.right.right⟩

theorem NatThree_prime : NatPrime NatThree := by
  exact CarmichaelUp.NatThree_prime

theorem NatEleven_prime : NatPrime NatEleven := by
  exact CarmichaelUp.NatEleven_prime

theorem NatSeventeen_prime : NatPrime NatSeventeen := by
  exact CarmichaelUp.NatSeventeen_prime

theorem NatThree_mul_NatEleven :
    NatMul NatThree NatEleven (natToUnary 33) := by
  exact CarmichaelUp.NatThree_mul_NatEleven

theorem NatThirtyThree_mul_NatSeventeen :
    NatMul (natToUnary 33) NatSeventeen
      NatFiveHundredSixtyOne := by
  exact CarmichaelUp.NatThirtyThree_mul_NatSeventeen

theorem carmichael561_factorization :
    PrimeFactorization NatFiveHundredSixtyOne
      [NatThree, NatEleven, NatSeventeen] := by
  exact CarmichaelUp.carmichael561_factorization

theorem carmichael561_squarefree :
    listSquarefree [NatThree, NatEleven, NatSeventeen] := by
  exact CarmichaelUp.carmichael561_squarefree

theorem three_minus_one_divides_560 :
    CarmichaelUp.PrimeFactorDividesPredecessor NatThree
      NatFiveHundredSixtyOne := by
  exact CarmichaelUp.three_minus_one_divides_560

theorem eleven_minus_one_divides_560 :
    CarmichaelUp.PrimeFactorDividesPredecessor NatEleven
      NatFiveHundredSixtyOne := by
  exact CarmichaelUp.eleven_minus_one_divides_560

theorem seventeen_minus_one_divides_560 :
    CarmichaelUp.PrimeFactorDividesPredecessor NatSeventeen
      NatFiveHundredSixtyOne := by
  exact CarmichaelUp.seventeen_minus_one_divides_560

theorem carmichael561_composite :
    CompositeNumber NatFiveHundredSixtyOne := by
  exact CarmichaelUp.carmichael561_composite

theorem carmichael561_korselt_factor_ledger :
    KorseltFactorLedger NatFiveHundredSixtyOne
      [NatThree, NatEleven, NatSeventeen] := by
  exact CarmichaelUp.carmichael561_korselt_factors

theorem carmichael561_korselt :
    KorseltCriterion NatFiveHundredSixtyOne
      [NatThree, NatEleven, NatSeventeen] := by
  exact CarmichaelUp.carmichael561_korselt

theorem carmichael561_verified_by_korselt :
    CompositeNumber NatFiveHundredSixtyOne ∧
      PrimeFactorization NatFiveHundredSixtyOne
        [NatThree, NatEleven, NatSeventeen] ∧
      listSquarefree [NatThree, NatEleven, NatSeventeen] ∧
        (∀ p : BHist, p ∈ [NatThree, NatEleven, NatSeventeen] ->
          CarmichaelUp.PrimeFactorDividesPredecessor p
            NatFiveHundredSixtyOne) := by
  exact korseltCriterion_components carmichael561_korselt

end BEDC.Derived.CarmichaelNumberUp
