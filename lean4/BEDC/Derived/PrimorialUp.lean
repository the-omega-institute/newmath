import BEDC.Derived.FactorialUp
import BEDC.Derived.PrimeUp.FactorialAbsorption

namespace BEDC.Derived.PrimorialUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp
open BEDC.Derived.IntUp (natMulFn natMulFn_rel)
open BEDC.Derived.PrimeUp
open BEDC.Derived.FactorialUp

abbrev NatOne : BHist := BHist.e1 BHist.Empty
abbrev NatTwo : BHist := BHist.e1 NatOne
abbrev NatThree : BHist := BHist.e1 NatTwo
abbrev NatSix : BHist :=
  BHist.e1 (BHist.e1 (BHist.e1 (BHist.e1 (BHist.e1 (BHist.e1 BHist.Empty)))))
abbrev NatSeven : BHist := BHist.e1 NatSix

inductive ListAll (P : BHist -> Prop) : List BHist -> Prop where
  | nil : ListAll P []
  | cons {x : BHist} {xs : List BHist} : P x -> ListAll P xs -> ListAll P (x :: xs)

inductive ListNodupByHsame : List BHist -> Prop where
  | nil : ListNodupByHsame []
  | cons {x : BHist} {xs : List BHist} :
      (∀ y : BHist, List.Mem y xs -> hsame x y -> False) ->
        ListNodupByHsame xs -> ListNodupByHsame (x :: xs)

inductive ListCountHsame (needle : BHist) : List BHist -> BHist -> Prop where
  | nil : ListCountHsame needle [] BHist.Empty
  | cons_same {x : BHist} {xs : List BHist} {tailCount count : BHist} :
      hsame needle x -> ListCountHsame needle xs tailCount ->
        NatAdd tailCount NatOne count -> ListCountHsame needle (x :: xs) count
  | cons_diff {x : BHist} {xs : List BHist} {tailCount : BHist} :
      (hsame needle x -> False) -> ListCountHsame needle xs tailCount ->
        ListCountHsame needle (x :: xs) tailCount

def primorialProduct : List BHist -> BHist
  | [] => NatOne
  | p :: ps => natMulFn p (primorialProduct ps)

def PrimorialProduct : List BHist -> BHist -> Prop
  | [], product => hsame product NatOne
  | p :: ps, product =>
      NatPrime p ∧ ∃ tail : BHist,
        PrimorialProduct ps tail ∧ NatMul p tail product

def PrimeSegment (bound product : BHist) (primes : List BHist) : Prop :=
  UnaryHistory bound ∧ ListNodupByHsame primes ∧
    (∀ p : BHist, List.Mem p primes ->
      NatPrime p ∧ (hsame p bound ∨ NatUnaryStrictPrefix p bound)) ∧
    PrimorialProduct primes product

inductive FirstPrimePrefixFrom : BHist -> List BHist -> Prop where
  | nil (lower : BHist) : FirstPrimePrefixFrom lower []
  | cons {lower p : BHist} {ps : List BHist} :
      NatPrime p -> NatUnaryStrictPrefix lower p ->
        (∀ q : BHist, NatPrime q -> NatUnaryStrictPrefix lower q ->
          NatUnaryStrictPrefix q p -> False) ->
        FirstPrimePrefixFrom p ps -> FirstPrimePrefixFrom lower (p :: ps)

def FirstPrimePrefix (primes : List BHist) : Prop :=
  FirstPrimePrefixFrom NatOne primes

def PrimePrefix (primes : List BHist) : Prop :=
  ListAll NatPrime primes ∧ ListNodupByHsame primes

def nthPrimorialProduct (primes : List BHist) : BHist :=
  primorialProduct primes

def euclidNumber (product : BHist) : BHist :=
  append product NatOne

def euclidNumberFromList (primes : List BHist) : BHist :=
  euclidNumber (primorialProduct primes)

theorem ListAll_tail {P : BHist -> Prop} {x : BHist} {xs : List BHist} :
    ListAll P (x :: xs) -> ListAll P xs := by
  intro all
  cases all with
  | cons _ tail => exact tail

theorem ListAll_head {P : BHist -> Prop} {x : BHist} {xs : List BHist} :
    ListAll P (x :: xs) -> P x := by
  intro all
  cases all with
  | cons head _tail => exact head

theorem ListNodupByHsame_tail {x : BHist} {xs : List BHist} :
    ListNodupByHsame (x :: xs) -> ListNodupByHsame xs := by
  intro nodup
  cases nodup with
  | cons _ tail => exact tail

theorem NatFactorial_to_NatFact {n f : BHist} :
    NatFactorial n f -> NatFact n f := by
  intro factorial
  induction factorial with
  | zero =>
      exact NatFact.zero
  | succ _previous step ih =>
      exact NatFact.succ ih step

theorem NatFact_to_NatFactorial {n f : BHist} :
    NatFact n f -> NatFactorial n f := by
  intro fact
  induction fact with
  | zero =>
      exact NatFactorial.zero
  | succ _previous step ih =>
      exact NatFactorial.succ ih step

theorem primorialProduct_nil :
    primorialProduct [] = NatOne := by
  rfl

theorem primorialProduct_cons (p : BHist) (ps : List BHist) :
    primorialProduct (p :: ps) = natMulFn p (primorialProduct ps) := by
  rfl

theorem PrimorialProduct_nil :
    PrimorialProduct [] NatOne := by
  rfl

theorem PrimorialProduct_cons {p tail product : BHist} {ps : List BHist} :
    NatPrime p -> PrimorialProduct ps tail -> NatMul p tail product ->
      PrimorialProduct (p :: ps) product := by
  intro pPrime tailProduct step
  exact And.intro pPrime (Exists.intro tail (And.intro tailProduct step))

theorem PrimorialProduct_result_unary :
    ∀ {ps : List BHist} {product : BHist},
      PrimorialProduct ps product -> UnaryHistory product
  | [], product, productCert =>
      unary_transport (unary_e1_closed unary_empty) (hsame_symm productCert)
  | p :: ps, product, productCert => by
      cases productCert with
      | intro pPrime tailData =>
          cases tailData with
          | intro tail tailCert =>
              exact NatMul_result_unary pPrime.left tailCert.right

theorem primorialProduct_certified :
    ∀ {ps : List BHist}, ListAll NatPrime ps -> PrimorialProduct ps (primorialProduct ps)
  | [], _all =>
      PrimorialProduct_nil
  | p :: ps, all => by
      have pPrime : NatPrime p := ListAll_head all
      have tailAll : ListAll NatPrime ps := ListAll_tail all
      have tailCert : PrimorialProduct ps (primorialProduct ps) :=
        primorialProduct_certified tailAll
      have tailUnary : UnaryHistory (primorialProduct ps) :=
        PrimorialProduct_result_unary tailCert
      exact PrimorialProduct_cons pPrime tailCert (natMulFn_rel pPrime.left tailUnary)

theorem primorialProduct_unary {ps : List BHist} :
    ListAll NatPrime ps -> UnaryHistory (primorialProduct ps) := by
  intro all
  exact PrimorialProduct_result_unary (primorialProduct_certified all)

theorem PrimorialProduct_functional :
    ∀ {ps : List BHist} {x y : BHist}, PrimorialProduct ps x -> PrimorialProduct ps y ->
      hsame x y
  | [], _x, _y, left, right =>
      hsame_trans left (hsame_symm right)
  | p :: ps, _x, _y, left, right => by
      cases left with
      | intro pPrime leftTail =>
          cases leftTail with
          | intro lx lxData =>
              cases right with
              | intro _pPrimeRight rightTail =>
                  cases rightTail with
                  | intro ry ryData =>
                      have sameTail : hsame lx ry :=
                        PrimorialProduct_functional lxData.left ryData.left
                      have shifted := NatMul_multiplier_hsame_transport lxData.right sameTail
                      exact NatMul_functional pPrime.left shifted.right ryData.right

theorem primorialProduct_spec {ps : List BHist} {product : BHist} :
    ListAll NatPrime ps -> PrimorialProduct ps product ->
      hsame (primorialProduct ps) product := by
  intro all productCert
  exact PrimorialProduct_functional (primorialProduct_certified all) productCert

theorem primorialProduct_cons_relation {p : BHist} {ps : List BHist} :
    NatPrime p -> ListAll NatPrime ps ->
      NatMul p (primorialProduct ps) (primorialProduct (p :: ps)) := by
  intro pPrime all
  change NatMul p (primorialProduct ps) (natMulFn p (primorialProduct ps))
  exact natMulFn_rel pPrime.left (primorialProduct_unary all)

theorem euclidNumber_add_one {product : BHist} :
    UnaryHistory product -> NatAdd product NatOne (euclidNumber product) := by
  intro productUnary
  exact And.intro productUnary
    (And.intro (unary_e1_closed unary_empty) (cont_intro rfl))

theorem euclidNumber_unary {product : BHist} :
    UnaryHistory product -> UnaryHistory (euclidNumber product) := by
  intro productUnary
  exact NatAdd_result_unary (euclidNumber_add_one productUnary)

theorem euclidNumberFromList_add_one {ps : List BHist} :
    ListAll NatPrime ps ->
      NatAdd (primorialProduct ps) NatOne (euclidNumberFromList ps) := by
  intro all
  exact euclidNumber_add_one (primorialProduct_unary all)

theorem PrimeSegment_product_unary {bound product : BHist} {primes : List BHist} :
    PrimeSegment bound product primes -> UnaryHistory product := by
  intro segment
  exact PrimorialProduct_result_unary segment.right.right.right

theorem primorial_empty_value :
    primorialProduct [] = NatOne := by
  rfl

theorem primorial_first_value :
    primorialProduct [NatTwo] = NatTwo := by
  rfl

theorem primorial_first_two_value :
    primorialProduct [NatTwo, NatThree] = NatSix := by
  rfl

theorem euclid_empty_value :
    euclidNumberFromList [] = NatTwo := by
  rfl

theorem euclid_first_value :
    euclidNumberFromList [NatTwo] = NatThree := by
  rfl

theorem euclid_first_two_value :
    euclidNumberFromList [NatTwo, NatThree] = NatSeven := by
  rfl

theorem primePrefix_two_three :
    ListAll NatPrime [NatTwo, NatThree] := by
  exact ListAll.cons NatPrime_first_pair.left
    (ListAll.cons NatPrime_first_pair.right ListAll.nil)

theorem primorial_first_two_factorial_three_hsame :
    hsame (primorialProduct [NatTwo, NatThree]) (natFactorialFn NatThree) := by
  rfl

theorem primorial_first_two_factorial_three_divides :
    NatDivides (primorialProduct [NatTwo, NatThree]) (natFactorialFn NatThree) := by
  exact (NatDivides_reflexive_pair
    (primorialProduct_unary primePrefix_two_three)).right

theorem PrimorialUp_constructive_export :
    (∀ {ps : List BHist}, ListAll NatPrime ps -> PrimorialProduct ps (primorialProduct ps)) ∧
      (∀ {ps : List BHist}, ListAll NatPrime ps -> UnaryHistory (primorialProduct ps)) ∧
      (∀ {p : BHist} {ps : List BHist}, NatPrime p -> ListAll NatPrime ps ->
        NatMul p (primorialProduct ps) (primorialProduct (p :: ps))) ∧
      (∀ {product : BHist}, UnaryHistory product ->
        NatAdd product NatOne (euclidNumber product)) ∧
      (primorialProduct [] = NatOne) ∧
      (primorialProduct [NatTwo] = NatTwo) ∧
      (euclidNumberFromList [] = NatTwo) := by
  constructor
  · intro ps all
    exact primorialProduct_certified all
  · constructor
    · intro ps all
      exact primorialProduct_unary all
    · constructor
      · intro p ps pPrime all
        exact primorialProduct_cons_relation pPrime all
      · constructor
        · intro product productUnary
          exact euclidNumber_add_one productUnary
        · constructor
          · exact primorial_empty_value
          · constructor
            · exact primorial_first_value
            · exact euclid_empty_value

end BEDC.Derived.PrimorialUp
