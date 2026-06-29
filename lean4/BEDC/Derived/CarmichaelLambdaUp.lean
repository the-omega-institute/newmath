import BEDC.Derived.EulerTheoremUp
import BEDC.Derived.PadicUp.IntegerTower

namespace BEDC.Derived.CarmichaelLambdaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.NatUp
open BEDC.Derived.IntUp
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.ArithmeticFnUp
open BEDC.Derived.EulerTheoremUp
open BEDC.Derived.ZModUp
open BEDC.Derived.ZModResidueList

private abbrev One : BHist := BEDC.Derived.PadicUp.NatOne

def CarmichaelExponentOfSystem {n : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (_system : ZModReducedResidueSystem n nUnary nNonempty)
    (lambda : BHist) : Prop :=
  UnaryHistory lambda ∧
    ∀ a : ZMod n,
      relUnit (zmodRelCommRing n nUnary nNonempty) a ->
        zmodEq
          (zmodPowByNat n nUnary nNonempty a (bwordLength lambda))
          (zmodOne n nUnary nNonempty)

def CarmichaelLambdaOfSystem {n : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (system : ZModReducedResidueSystem n nUnary nNonempty)
    (lambda : BHist) : Prop :=
  CarmichaelExponentOfSystem nUnary nNonempty system lambda ∧
    ∀ candidate : BHist,
      CarmichaelExponentOfSystem nUnary nNonempty system candidate ->
        NatDivides lambda candidate

inductive CarmichaelLambdaPrimePowerFormula
    (p : BHist) (k lambda : BHist) : Prop where
  | oddOrSmallExponent
      (pPrime : NatPrime p)
      (kPositive : NatUnaryStrictPrefix BHist.Empty k)
      (notTwoLarge :
        hsame p (natToUnary 2) ->
          NatUnaryStrictPrefix (natToUnary 2) k -> False)
      (kPred : BHist)
      (kPredSpec : bwordLength kPred = bwordLength k - 1)
      (formula :
        hsame lambda
          (natMulFn (pPowCanon p kPred)
            (natSubUnary p One))) :
      CarmichaelLambdaPrimePowerFormula p k lambda
  | twoLargeExponent
      (pIsTwo : hsame p (natToUnary 2))
      (kLarge : NatUnaryStrictPrefix (natToUnary 2) k)
      (kShift : BHist)
      (kShiftSpec : bwordLength kShift = bwordLength k - 2)
      (formula :
        hsame lambda (pPowCanon (natToUnary 2) kShift)) :
      CarmichaelLambdaPrimePowerFormula p k lambda

theorem carmichaelExponent_unary {n : BHist}
    {nUnary : UnaryHistory n}
    {nNonempty : hsame n BHist.Empty -> False}
    {system : ZModReducedResidueSystem n nUnary nNonempty}
    {lambda : BHist} :
    CarmichaelExponentOfSystem nUnary nNonempty system lambda ->
      UnaryHistory lambda := by
  intro exponent
  exact exponent.left

theorem carmichaelLambda_unary {n : BHist}
    {nUnary : UnaryHistory n}
    {nNonempty : hsame n BHist.Empty -> False}
    {system : ZModReducedResidueSystem n nUnary nNonempty}
    {lambda : BHist} :
    CarmichaelLambdaOfSystem nUnary nNonempty system lambda ->
      UnaryHistory lambda := by
  intro lambdaCert
  exact carmichaelExponent_unary lambdaCert.left

theorem zmod_pow_carmichaelExponent_eq_one {n : BHist}
    {nUnary : UnaryHistory n}
    {nNonempty : hsame n BHist.Empty -> False}
    {system : ZModReducedResidueSystem n nUnary nNonempty}
    {lambda : BHist}
    (exponent : CarmichaelExponentOfSystem nUnary nNonempty system lambda)
    (a : ZMod n) :
    relUnit (zmodRelCommRing n nUnary nNonempty) a ->
      zmodEq
        (zmodPowByNat n nUnary nNonempty a (bwordLength lambda))
        (zmodOne n nUnary nNonempty) := by
  intro aUnit
  exact exponent.right a aUnit

theorem zmod_pow_carmichaelLambda_eq_one {n : BHist}
    {nUnary : UnaryHistory n}
    {nNonempty : hsame n BHist.Empty -> False}
    {system : ZModReducedResidueSystem n nUnary nNonempty}
    {lambda : BHist}
    (lambdaCert : CarmichaelLambdaOfSystem nUnary nNonempty system lambda)
    (a : ZMod n) :
    relUnit (zmodRelCommRing n nUnary nNonempty) a ->
      zmodEq
        (zmodPowByNat n nUnary nNonempty a (bwordLength lambda))
        (zmodOne n nUnary nNonempty) := by
  intro aUnit
  exact zmod_pow_carmichaelExponent_eq_one lambdaCert.left a aUnit

theorem carmichaelLambda_divides_any_exponent {n : BHist}
    {nUnary : UnaryHistory n}
    {nNonempty : hsame n BHist.Empty -> False}
    {system : ZModReducedResidueSystem n nUnary nNonempty}
    {lambda candidate : BHist} :
    CarmichaelLambdaOfSystem nUnary nNonempty system lambda ->
      CarmichaelExponentOfSystem nUnary nNonempty system candidate ->
        NatDivides lambda candidate := by
  intro lambdaCert candidateExponent
  exact lambdaCert.right candidate candidateExponent

theorem eulerPhi_is_carmichaelExponent {n : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (system : ZModReducedResidueSystem n nUnary nNonempty) :
    CarmichaelExponentOfSystem nUnary nNonempty system
      (eulerPhiFactors system.factors) := by
  constructor
  · exact eulerPhiFactors_unary system.factors
  · intro a aUnit
    unfold eulerPhiFactors
    rw [natToUnary_length]
    exact zmod_eulerPhi_from_reducedResidueSystem nUnary nNonempty a system aUnit

theorem carmichaelLambda_divides_eulerPhi {n : BHist}
    {nUnary : UnaryHistory n}
    {nNonempty : hsame n BHist.Empty -> False}
    {system : ZModReducedResidueSystem n nUnary nNonempty}
    {lambda : BHist} :
    CarmichaelLambdaOfSystem nUnary nNonempty system lambda ->
      NatDivides lambda (eulerPhiFactors system.factors) := by
  intro lambdaCert
  exact carmichaelLambda_divides_any_exponent lambdaCert
    (eulerPhi_is_carmichaelExponent nUnary nNonempty system)

theorem carmichaelPrimePowerFormula_unary {p k lambda : BHist} :
    CarmichaelLambdaPrimePowerFormula p k lambda ->
      UnaryHistory lambda := by
  intro formula
  cases formula with
  | oddOrSmallExponent pPrime _ _ kPred _ formulaEq =>
      exact unary_transport
        (natMulFn_unary
          (pPowCanon_unary p kPred)
          (natSubUnary_unary pPrime.left))
        (hsame_symm formulaEq)
  | twoLargeExponent _ _ kShift _ formulaEq =>
      exact unary_transport
        (pPowCanon_unary (natToUnary 2) kShift)
        (hsame_symm formulaEq)

theorem carmichaelPrimePowerFormula_components {p k lambda : BHist} :
    CarmichaelLambdaPrimePowerFormula p k lambda ->
      (∃ kPred : BHist,
        NatPrime p ∧ NatUnaryStrictPrefix BHist.Empty k ∧
          bwordLength kPred = bwordLength k - 1 ∧
            hsame lambda
              (natMulFn (pPowCanon p kPred)
                (natSubUnary p One))) ∨
      (∃ kShift : BHist,
        hsame p (natToUnary 2) ∧ NatUnaryStrictPrefix (natToUnary 2) k ∧
          bwordLength kShift = bwordLength k - 2 ∧
            hsame lambda (pPowCanon (natToUnary 2) kShift)) := by
  intro formula
  cases formula with
  | oddOrSmallExponent pPrime kPositive _ kPred kPredSpec formulaEq =>
      exact Or.inl ⟨kPred, pPrime, kPositive, kPredSpec, formulaEq⟩
  | twoLargeExponent pIsTwo kLarge kShift kShiftSpec formulaEq =>
      exact Or.inr ⟨kShift, pIsTwo, kLarge, kShiftSpec, formulaEq⟩

end BEDC.Derived.CarmichaelLambdaUp
