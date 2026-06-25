import BEDC.Derived.LegendreUp
import BEDC.Derived.PrimeUp.UniqueFactorization
import BEDC.Derived.IntUp.CommRing
import BEDC.Algebra.Rel.IntegerUp

namespace BEDC.Derived.JacobiUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.ZModUp
open BEDC.Derived.LegendreUp

abbrev IntegerUp := BEDC.Algebra.Rel.IntegerUp
abbrev IntEq := BEDC.Algebra.Rel.IntEq
abbrev IntMul := BEDC.Algebra.Rel.IntMul

def jacobiOne : IntegerUp :=
  BEDC.Algebra.Rel.intOne

def jacobiMul : IntegerUp -> IntegerUp -> IntegerUp :=
  BEDC.Algebra.Rel.IntMul

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
    IntEq a a' -> IntEq b b' ->
      IntEq (jacobiMul a b) (jacobiMul a' b') := by
  intro left right
  exact intRing.mul_congr left right

private theorem intMul_assoc (a b c : IntegerUp) :
    IntEq (jacobiMul (jacobiMul a b) c)
      (jacobiMul a (jacobiMul b c)) :=
  intRing.mul_assoc a b c

private theorem intMul_one (a : IntegerUp) :
    IntEq (jacobiMul a jacobiOne) a :=
  intRing.mul_one a

private theorem intMul_one_left (a : IntegerUp) :
    IntEq (jacobiMul jacobiOne a) a :=
  intRing.one_mul a

private theorem intMul_two_by_two_swap (a b c d : IntegerUp) :
    IntEq (jacobiMul (jacobiMul a b) (jacobiMul c d))
      (jacobiMul (jacobiMul a c) (jacobiMul b d)) := by
  exact intRing.trans (intRing.mul_assoc a b (jacobiMul c d))
    (intRing.trans
      (intRing.mul_congr (intRing.refl a)
        (intRing.trans (intRing.symm (intRing.mul_assoc b c d))
          (intRing.trans
            (intRing.mul_congr (intRing.mul_comm b c) (intRing.refl d))
            (intRing.mul_assoc c b d))))
      (intRing.symm (intRing.mul_assoc a c (jacobiMul b d))))

abbrev PrimeResidueAssignment :=
  (p : BHist) -> ZMod p

def LegendreAt (a : PrimeResidueAssignment) (p : BHist) (s : IntegerUp) : Prop :=
  ∃ prime : NatPrime p, legendreSym prime (a p) s

def JacobiProduct (a : PrimeResidueAssignment) :
    List BHist -> IntegerUp -> Prop
  | [], value => IntEq value jacobiOne
  | p :: ps, value =>
      ∃ head tail : IntegerUp,
        LegendreAt a p head ∧ JacobiProduct a ps tail ∧
          IntEq value (jacobiMul head tail)

def JacobiSymbol (a : PrimeResidueAssignment)
    (n : BHist) (value : IntegerUp) : Prop :=
  ∃ factors : List BHist, PrimeFactorizationProduct factors n ∧
    JacobiProduct a factors value

def OddPrimeFactor (p : BHist) : Prop :=
  ∃ tail : BHist, hsame p (BHist.e1 (BHist.e1 tail)) ∧ UnaryHistory tail

def OddPrimeFactorList : List BHist -> Prop
  | [] => True
  | p :: ps => OddPrimeFactor p ∧ OddPrimeFactorList ps

def CompositePrimeFactorList : List BHist -> Prop
  | [] => False
  | [_p] => False
  | _p :: _q :: _ps => True

def JacobiOddCompositeDenominator
    (a : PrimeResidueAssignment)
    (n : BHist) (value : IntegerUp) : Prop :=
  ∃ factors : List BHist, PrimeFactorizationProduct factors n ∧
    OddPrimeFactorList factors ∧ CompositePrimeFactorList factors ∧
      JacobiProduct a factors value

theorem OddPrimeFactor_of_prime {p : BHist} :
    NatPrime p -> OddPrimeFactor p :=
  NatPrime_strict_unit_successor_shape

theorem JacobiProduct_nil :
    JacobiProduct (a := a) [] jacobiOne := by
  exact intEq_refl jacobiOne

theorem JacobiProduct_congr {a : PrimeResidueAssignment}
    {factors : List BHist} {x y : IntegerUp} :
    IntEq x y -> JacobiProduct a factors y -> JacobiProduct a factors x := by
  intro same product
  induction factors generalizing x y with
  | nil =>
      change IntEq y jacobiOne at product
      change IntEq x jacobiOne
      exact intEq_trans same product
  | cons p ps ih =>
      cases product with
      | intro head headRest =>
          cases headRest with
          | intro tail data =>
              exact ⟨head, tail, data.left, data.right.left,
                intEq_trans same data.right.right⟩

theorem JacobiProduct_cons {a : PrimeResidueAssignment}
    {p : BHist} {ps : List BHist} {head tail value : IntegerUp} :
    LegendreAt a p head -> JacobiProduct a ps tail ->
      IntEq value (jacobiMul head tail) ->
        JacobiProduct a (p :: ps) value := by
  intro headLeg tailJac valueEq
  exact ⟨head, tail, headLeg, tailJac, valueEq⟩

theorem JacobiProduct_single {a : PrimeResidueAssignment}
    {p : BHist} {value : IntegerUp} :
    LegendreAt a p value -> JacobiProduct a [p] value := by
  intro leg
  refine JacobiProduct_cons leg JacobiProduct_nil ?_
  exact intEq_symm (intMul_one value)

theorem jacobiProduct_append {a : PrimeResidueAssignment}
    {left right : List BHist} {leftValue rightValue : IntegerUp} :
    JacobiProduct a left leftValue -> JacobiProduct a right rightValue ->
      JacobiProduct a (left ++ right) (jacobiMul leftValue rightValue) := by
  intro leftJac rightJac
  induction left generalizing leftValue with
  | nil =>
      change IntEq leftValue jacobiOne at leftJac
      change JacobiProduct a right (jacobiMul leftValue rightValue)
      exact JacobiProduct_congr
        (intEq_trans
          (intMul_respects leftJac (intEq_refl rightValue))
          (intMul_one_left rightValue))
        rightJac
  | cons p ps ih =>
      cases leftJac with
      | intro head headRest =>
          cases headRest with
          | intro tail rest =>
              cases rest with
              | intro headLeg rest2 =>
                  cases rest2 with
                  | intro tailJac valueEq =>
                      have tailApp :
                          JacobiProduct a (ps ++ right)
                            (jacobiMul tail rightValue) :=
                        ih tailJac
                      refine JacobiProduct_cons headLeg tailApp ?_
                      exact intEq_trans
                        (intMul_respects valueEq (intEq_refl rightValue))
                        (intMul_assoc head tail rightValue)

theorem jacobiProduct_denominator_mul {a : PrimeResidueAssignment}
    {left right : List BHist} {leftValue rightValue value : IntegerUp} :
    JacobiProduct a left leftValue -> JacobiProduct a right rightValue ->
      IntEq value (jacobiMul leftValue rightValue) ->
        JacobiProduct a (left ++ right) value := by
  intro leftJac rightJac valueEq
  exact JacobiProduct_congr valueEq (jacobiProduct_append leftJac rightJac)

theorem primeFactorizationProduct_append {left right : List BHist}
    {m n mn : BHist} :
    PrimeFactorizationProduct left m -> PrimeFactorizationProduct right n ->
      NatMul m n mn -> PrimeFactorizationProduct (left ++ right) mn := by
  intro leftProduct rightProduct productMN
  induction left generalizing m mn with
  | nil =>
      have sameMUnit : hsame m NatOne := leftProduct
      have productUnit : NatMul NatOne n mn :=
        (NatMul_multiplicand_hsame_transport sameMUnit productMN).right
      exact PrimeFactorizationProduct_result_hsame_transport rightProduct
        (hsame_symm
          (NatMul_unit_left_hsame
            (PrimeFactorizationProduct_result_unary rightProduct) productUnit))
  | cons p ps ih =>
      cases leftProduct with
      | intro pPrime pRest =>
          cases pRest with
          | intro tailProduct tailData =>
              have tailRightProduct : PrimeFactorizationProduct (ps ++ right)
                  (natMulFn tailProduct n) := by
                exact ih tailData.left (natMulFn_rel
                  (PrimeFactorizationProduct_result_unary tailData.left)
                  (PrimeFactorizationProduct_result_unary rightProduct))
              have pTimesTailRight :
                  NatMul p (natMulFn tailProduct n) mn := by
                have displayedTailRight :
                    NatMul tailProduct n (natMulFn tailProduct n) :=
                  natMulFn_rel
                    (PrimeFactorizationProduct_result_unary tailData.left)
                    (PrimeFactorizationProduct_result_unary rightProduct)
                have displayedPTailRight :
                    NatMul p (natMulFn tailProduct n)
                      (natMulFn p (natMulFn tailProduct n)) :=
                  natMulFn_rel pPrime.left
                    (NatMul_result_unary
                      (PrimeFactorizationProduct_result_unary tailData.left)
                      displayedTailRight)
                have sameAssoc :
                    hsame mn (natMulFn p (natMulFn tailProduct n)) :=
                  NatMul_assoc_hsame pPrime.left
                    (PrimeFactorizationProduct_result_unary tailData.left)
                    (PrimeFactorizationProduct_result_unary rightProduct)
                    tailData.right productMN displayedTailRight
                    displayedPTailRight
                exact (NatMul_result_hsame_transport displayedPTailRight
                  (hsame_symm sameAssoc)).right
              exact ⟨pPrime, natMulFn tailProduct n, tailRightProduct,
                pTimesTailRight⟩

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
          exact ⟨leftFactors ++ rightFactors,
            primeFactorizationProduct_append leftData.left rightData.left productMN,
            jacobiProduct_append leftData.right rightData.right⟩

theorem primeFactorizationProduct_single {p : BHist} :
    NatPrime p -> PrimeFactorizationProduct [p] p := by
  intro prime
  exact ⟨prime, NatOne, hsame_refl NatOne,
    (NatMul_unit_right_iff prime.left).mpr (hsame_refl p)⟩

theorem jacobiProduct_prime_consistent {a : PrimeResidueAssignment}
    {p : BHist} {value : IntegerUp} (prime : NatPrime p) :
    legendreSym prime (a p) value -> JacobiProduct a [p] value := by
  intro leg
  exact JacobiProduct_single ⟨prime, leg⟩

theorem jacobiSymbol_prime_consistent {a : PrimeResidueAssignment}
    {p : BHist} {value : IntegerUp} (prime : NatPrime p) :
    legendreSym prime (a p) value -> JacobiSymbol a p value := by
  intro leg
  exact ⟨[p], primeFactorizationProduct_single prime,
    jacobiProduct_prime_consistent prime leg⟩

def LegendrePointwiseMul
    (a b ab : PrimeResidueAssignment)
    (factors : List BHist) : Prop :=
  ∀ p : BHist, p ∈ factors ->
    ∀ sa sb : IntegerUp,
      LegendreAt a p sa -> LegendreAt b p sb ->
        LegendreAt ab p (jacobiMul sa sb)

theorem jacobiProduct_numerator_mul
    {a b ab : PrimeResidueAssignment}
    {factors : List BHist} {va vb : IntegerUp} :
    LegendrePointwiseMul a b ab factors ->
      JacobiProduct a factors va -> JacobiProduct b factors vb ->
        JacobiProduct ab factors (jacobiMul va vb) := by
  intro pointwise leftJac rightJac
  induction factors generalizing va vb with
  | nil =>
      change IntEq va jacobiOne at leftJac
      change IntEq vb jacobiOne at rightJac
      change IntEq (jacobiMul va vb) jacobiOne
      exact intEq_trans
        (intMul_respects leftJac rightJac)
        (intMul_one jacobiOne)
  | cons p ps ih =>
      cases leftJac with
      | intro ha haRest =>
          cases haRest with
          | intro ta leftRest =>
              cases leftRest with
              | intro haLeg leftRest2 =>
                  cases leftRest2 with
                  | intro taJac vaEq =>
                      cases rightJac with
                      | intro hb hbRest =>
                          cases hbRest with
                          | intro tb rightRest =>
                              cases rightRest with
                              | intro hbLeg rightRest2 =>
                                  cases rightRest2 with
                                  | intro tbJac vbEq =>
                                      have headMul :
                                          LegendreAt ab p (jacobiMul ha hb) :=
                                        pointwise p (List.Mem.head ps) ha hb haLeg hbLeg
                                      have tailPointwise :
                                          LegendrePointwiseMul a b ab ps := by
                                        intro q qMem
                                        exact pointwise q (List.Mem.tail p qMem)
                                      have tailMul :
                                          JacobiProduct ab ps (jacobiMul ta tb) :=
                                        ih tailPointwise taJac tbJac
                                      refine JacobiProduct_cons headMul tailMul ?_
                                      exact intEq_trans
                                        (intMul_respects vaEq vbEq)
                                        (intMul_two_by_two_swap ha ta hb tb)

end BEDC.Derived.JacobiUp
