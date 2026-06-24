import BEDC.Derived.GcdUp
import BEDC.Derived.PrimeUp.UniqueFactorization

namespace BEDC.Derived.ArithmeticFnUp

open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.GcdUp

def natPow (base exp : Nat) : Nat :=
  match exp with
  | 0 => 1
  | exp' + 1 => base * natPow base exp'

private theorem nat_mul_assoc_pure (a b c : Nat) :
    (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      calc
        (a * b) * Nat.succ c = (a * b) * c + a * b := Nat.mul_succ (a * b) c
        _ = a * (b * c) + a * b := congrArg (fun x => x + a * b) ih
        _ = a * (b * c + b) := (Nat.mul_add a (b * c) b).symm
        _ = a * (b * Nat.succ c) := congrArg (fun x => a * x) (Nat.mul_succ b c).symm

def listPrimeCountNat (p : BHist) : List BHist -> Nat
  | [] => 0
  | q :: qs =>
      if p = q then listPrimeCountNat p qs + 1 else listPrimeCountNat p qs

def listRemovePrime (p : BHist) : List BHist -> List BHist
  | [] => []
  | q :: qs => if p = q then listRemovePrime p qs else q :: listRemovePrime p qs

def listContainsPrime (p : BHist) : List BHist -> Bool
  | [] => false
  | q :: qs => if p = q then true else listContainsPrime p qs

def listNoCommonPrime : List BHist -> List BHist -> Prop
  | [], _ => True
  | p :: ps, qs => listContainsPrime p qs = false ∧ listNoCommonPrime ps qs

def listSquarefree : List BHist -> Prop
  | [] => True
  | p :: ps => listContainsPrime p ps = false ∧ listSquarefree ps

def eulerFactorNat (p : BHist) (k : Nat) : Nat :=
  match k with
  | 0 => 1
  | k' + 1 => natPow (bwordLength p) k' * (bwordLength p - 1)

def sigmaFactorNat (p : BHist) (k : Nat) : Nat :=
  match k with
  | 0 => 1
  | k' + 1 => sigmaFactorNat p k' + natPow (bwordLength p) (k' + 1)

def eulerPhiFactorsNat : List BHist -> Nat
  | [] => 1
  | p :: ps =>
      if listContainsPrime p ps then bwordLength p * eulerPhiFactorsNat ps
      else (bwordLength p - 1) * eulerPhiFactorsNat ps

def sigmaFactorsNatFrom (entries : List BHist) : List BHist -> Nat
  | [] => 1
  | p :: ps =>
      if listContainsPrime p ps then sigmaFactorsNatFrom entries ps
      else sigmaFactorNat p (listPrimeCountNat p entries) *
        sigmaFactorsNatFrom entries ps

def sigmaFactorsNat (entries : List BHist) : Nat :=
  sigmaFactorsNatFrom entries entries

def mobiusFactorsInt : List BHist -> _root_.Int
  | [] => 1
  | p :: ps => if listContainsPrime p ps then 0 else -mobiusFactorsInt ps

def eulerPhiFactors (entries : List BHist) : BHist :=
  natToUnary (eulerPhiFactorsNat entries)

def sigmaFactors (entries : List BHist) : BHist :=
  natToUnary (sigmaFactorsNat entries)

def EulerPhiOfFactorization (n phi : BHist) : Prop :=
  ∃ entries : List BHist,
    PrimeFactorization n entries ∧ hsame phi (eulerPhiFactors entries)

def DivisorSigmaOfFactorization (n sigma : BHist) : Prop :=
  ∃ entries : List BHist,
    PrimeFactorization n entries ∧ hsame sigma (sigmaFactors entries)

def MobiusOfFactorization (n : BHist) (mu : _root_.Int) : Prop :=
  ∃ entries : List BHist,
    PrimeFactorization n entries ∧ mu = mobiusFactorsInt entries

def NatCoprimeByGcd (m n : BHist) : Prop :=
  NatGcd m n NatOne

theorem eulerPhiFactors_unary (entries : List BHist) :
    UnaryHistory (eulerPhiFactors entries) := by
  unfold eulerPhiFactors
  exact natToUnary_unary _

theorem sigmaFactors_unary (entries : List BHist) :
    UnaryHistory (sigmaFactors entries) := by
  unfold sigmaFactors
  exact natToUnary_unary _

theorem mobiusFactorsInt_repeated_zero {p : BHist} {ps : List BHist} :
    listContainsPrime p ps = true -> mobiusFactorsInt (p :: ps) = 0 := by
  intro member
  change (if listContainsPrime p ps then 0 else -mobiusFactorsInt ps) = 0
  rw [member]
  rfl

private theorem listContainsPrime_append_true_left {p : BHist} :
    ∀ xs ys : List BHist,
      listContainsPrime p xs = true -> listContainsPrime p (xs ++ ys) = true := by
  intro xs
  induction xs with
  | nil =>
      intro ys found
      cases found
  | cons q qs ih =>
      intro ys found
      change (if p = q then true else listContainsPrime p qs) = true at found
      change (if p = q then true else listContainsPrime p (qs ++ ys)) = true
      by_cases same : p = q
      · rw [if_pos same]
      · rw [if_neg same] at found
        rw [if_neg same]
        exact ih ys found

private theorem listContainsPrime_append_false {p : BHist} :
    ∀ xs ys : List BHist,
      listContainsPrime p xs = false -> listContainsPrime p ys = false ->
        listContainsPrime p (xs ++ ys) = false := by
  intro xs
  induction xs with
  | nil =>
      intro ys _absentLeft absentRight
      exact absentRight
  | cons q qs ih =>
      intro ys absentLeft absentRight
      change (if p = q then true else listContainsPrime p qs) = false at absentLeft
      change (if p = q then true else listContainsPrime p (qs ++ ys)) = false
      by_cases same : p = q
      · rw [if_pos same] at absentLeft
        cases absentLeft
      · rw [if_neg same] at absentLeft
        rw [if_neg same]
        exact ih ys absentLeft absentRight

theorem eulerPhiFactorsNat_append_disjoint
    (xs ys : List BHist) :
    listNoCommonPrime xs ys ->
      eulerPhiFactorsNat (xs ++ ys) =
        eulerPhiFactorsNat xs * eulerPhiFactorsNat ys := by
  intro common
  induction xs with
  | nil =>
      change eulerPhiFactorsNat ys = 1 * eulerPhiFactorsNat ys
      rw [Nat.one_mul]
  | cons p ps ih =>
      unfold listNoCommonPrime at common
      change
        (if listContainsPrime p (ps ++ ys)
          then bwordLength p * eulerPhiFactorsNat (ps ++ ys)
          else (bwordLength p - 1) * eulerPhiFactorsNat (ps ++ ys)) =
            (if listContainsPrime p ps
              then bwordLength p * eulerPhiFactorsNat ps
              else (bwordLength p - 1) * eulerPhiFactorsNat ps) *
                eulerPhiFactorsNat ys
      cases memPs : listContainsPrime p ps
      · have notAppend : listContainsPrime p (ps ++ ys) = false :=
          listContainsPrime_append_false ps ys memPs common.left
        rw [notAppend]
        change
          (bwordLength p - 1) * eulerPhiFactorsNat (ps ++ ys) =
            ((bwordLength p - 1) * eulerPhiFactorsNat ps) *
              eulerPhiFactorsNat ys
        rw [ih common.right]
        exact (nat_mul_assoc_pure (bwordLength p - 1)
          (eulerPhiFactorsNat ps) (eulerPhiFactorsNat ys)).symm
      · have memAppend : listContainsPrime p (ps ++ ys) = true :=
          listContainsPrime_append_true_left ps ys memPs
        rw [memAppend]
        change
          bwordLength p * eulerPhiFactorsNat (ps ++ ys) =
            (bwordLength p * eulerPhiFactorsNat ps) *
              eulerPhiFactorsNat ys
        rw [ih common.right]
        exact (nat_mul_assoc_pure (bwordLength p)
          (eulerPhiFactorsNat ps) (eulerPhiFactorsNat ys)).symm

theorem eulerPhiFactors_append_disjoint_hsame
    (xs ys : List BHist) :
    listNoCommonPrime xs ys ->
      hsame (eulerPhiFactors (xs ++ ys))
        (natToUnary (eulerPhiFactorsNat xs * eulerPhiFactorsNat ys)) := by
  intro common
  unfold eulerPhiFactors
  exact congrArg natToUnary (eulerPhiFactorsNat_append_disjoint xs ys common)

theorem PrimeFactorizationProduct_append_mul
    {xs ys : List BHist} {m n mn : BHist} :
    PrimeFactorizationProduct xs m ->
      PrimeFactorizationProduct ys n ->
        NatMul m n mn ->
          PrimeFactorizationProduct (xs ++ ys) mn := by
  intro fx fy mul
  induction xs generalizing m mn with
  | nil =>
      have mUnit : hsame m NatOne := fx
      have shifted : NatMul NatOne n mn :=
        (NatMul_multiplicand_hsame_transport mUnit mul).right
      have sameNMn : hsame n mn :=
        hsame_symm (NatMul_unit_left_hsame
          (PrimeFactorizationProduct_result_unary fy) shifted)
      exact PrimeFactorizationProduct_result_hsame_transport fy sameNMn
  | cons p ps ih =>
      cases fx with
      | intro pPrime tailWitness =>
          cases tailWitness with
          | intro tailProduct tailData =>
              have tailUnary : UnaryHistory tailProduct :=
                PrimeFactorizationProduct_result_unary tailData.left
              have nUnary : UnaryHistory n :=
                PrimeFactorizationProduct_result_unary fy
              cases NatMul_total tailUnary nUnary with
              | intro tailN tailNData =>
                  have tailProductFactor :
                      PrimeFactorizationProduct (ps ++ ys) tailN :=
                    ih tailData.left tailNData.right
                  have tailNUnary : UnaryHistory tailN := tailNData.left
                  cases NatMul_total pPrime.left tailNUnary with
                  | intro displayed displayedData =>
                      have sameMnDisplayed : hsame mn displayed :=
                        NatMul_assoc_hsame pPrime.left tailUnary nUnary
                          tailData.right mul tailNData.right displayedData.right
                      have pTailNAtMn : NatMul p tailN mn :=
                        (NatMul_result_hsame_transport displayedData.right
                          (hsame_symm sameMnDisplayed)).right
                      exact ⟨pPrime, tailN, tailProductFactor, pTailNAtMn⟩

theorem listContainsPrime_product_divides
    {p : BHist} {xs : List BHist} {n : BHist} :
    listContainsPrime p xs = true ->
      PrimeFactorizationProduct xs n ->
        NatDivides p n := by
  intro found product
  induction xs generalizing n with
  | nil =>
      cases found
  | cons q qs ih =>
      change (if p = q then true else listContainsPrime p qs) = true at found
      cases product with
      | intro qPrime tailWitness =>
          cases tailWitness with
          | intro tailProduct tailData =>
              by_cases same : p = q
              · rw [if_pos same] at found
                have qDividesN : NatDivides q n :=
                  ⟨tailProduct, PrimeFactorizationProduct_result_unary tailData.left,
                    tailData.right⟩
                exact (NatDivides_divisor_hsame_transport qDividesN (hsame_symm same)).right
              · rw [if_neg same] at found
                have pDividesTail : NatDivides p tailProduct :=
                  ih found tailData.left
                cases NatMul_total
                    (PrimeFactorizationProduct_result_unary tailData.left) qPrime.left with
                | intro displayed displayedData =>
                    have sameDisplayedN : hsame displayed n :=
                      NatMul_comm_hsame
                        (PrimeFactorizationProduct_result_unary tailData.left)
                        qPrime.left displayedData.right tailData.right
                    have tailQProduct : NatMul tailProduct q n :=
                      (NatMul_result_hsame_transport displayedData.right sameDisplayedN).right
                    exact NatDivides_mul_right_factor_closed qPrime.left
                      pDividesTail tailQProduct

private theorem listContainsPrime_false_of_not_divides
    {p : BHist} {xs : List BHist} {n : BHist} :
    PrimeFactorizationProduct xs n ->
      (NatDivides p n -> False) ->
        listContainsPrime p xs = false := by
  intro product notDivides
  cases found : listContainsPrime p xs
  · rfl
  · exact False.elim (notDivides (listContainsPrime_product_divides found product))

theorem PrimeFactorizationProduct_coprime_no_common
    {m n : BHist} {xs ys : List BHist} :
    PrimeFactorizationProduct xs m ->
      PrimeFactorizationProduct ys n ->
        NatGcd m n NatOne ->
          listNoCommonPrime xs ys := by
  intro fx fy gcd
  induction xs generalizing m with
  | nil =>
      trivial
  | cons p ps ih =>
      cases fx with
      | intro pPrime tailWitness =>
          cases tailWitness with
          | intro tailProduct tailData =>
              unfold listNoCommonPrime
              constructor
              · have pDividesM : NatDivides p m :=
                  ⟨tailProduct, PrimeFactorizationProduct_result_unary tailData.left,
                    tailData.right⟩
                have notDividesN : NatDivides p n -> False := by
                  intro pDividesN
                  have pDividesUnit : NatDivides p NatOne :=
                    NatGcd_greatest gcd pDividesM pDividesN
                  have pUnit : hsame p NatOne :=
                    (NatDivides_unit_right_iff.mp pDividesUnit)
                  cases pUnit
                  exact NatPrime_unit_absurd pPrime
                exact listContainsPrime_false_of_not_divides fy notDividesN
              · have tailDividesM : NatDivides tailProduct m :=
                  NatDivides_mul_right_closed pPrime.left
                    (PrimeFactorizationProduct_result_unary tailData.left)
                    tailData.right
                have tailGcd : NatGcd tailProduct n NatOne := by
                  constructor
                  · exact PrimeFactorizationProduct_result_unary tailData.left
                  · constructor
                    · exact NatGcd_right_unary gcd
                    · constructor
                      · exact NatGcd_result_unary gcd
                      · constructor
                        · exact (NatDivides_reflexive_pair
                            (PrimeFactorizationProduct_result_unary tailData.left)).left
                        · constructor
                          · exact NatGcd_dvd_right gcd
                          · intro d dividesTail dividesN
                            exact NatGcd_greatest gcd
                              (NatDivides_transitive dividesTail tailDividesM) dividesN
                exact ih tailData.left tailGcd

theorem eulerPhi_factorization_product_multiplicative
    {m n mn : BHist} {xs ys : List BHist} :
    PrimeFactorizationProduct xs m ->
      PrimeFactorizationProduct ys n ->
        NatMul m n mn ->
          listNoCommonPrime xs ys ->
            EulerPhiOfFactorization mn
              (natToUnary (eulerPhiFactorsNat xs * eulerPhiFactorsNat ys)) := by
  intro fx fy mul common
  have product : PrimeFactorizationProduct (xs ++ ys) mn :=
    PrimeFactorizationProduct_append_mul fx fy mul
  exact ⟨xs ++ ys,
    ⟨NatMul_result_unary (PrimeFactorizationProduct_result_unary fx) mul, product⟩,
    hsame_symm (eulerPhiFactors_append_disjoint_hsame xs ys common)⟩

theorem eulerPhi_factorization_product_multiplicative_of_gcd_one
    {m n mn : BHist} {xs ys : List BHist} :
    PrimeFactorizationProduct xs m ->
      PrimeFactorizationProduct ys n ->
        NatMul m n mn ->
          NatGcd m n NatOne ->
            EulerPhiOfFactorization mn
              (natToUnary (eulerPhiFactorsNat xs * eulerPhiFactorsNat ys)) := by
  intro fx fy mul gcd
  exact eulerPhi_factorization_product_multiplicative fx fy mul
    (PrimeFactorizationProduct_coprime_no_common fx fy gcd)

end BEDC.Derived.ArithmeticFnUp
