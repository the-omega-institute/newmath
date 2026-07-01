import BEDC.Derived.RHRoute.HalfPlaneEulerProduct
import BEDC.Derived.PrimeUp.UniqueFactorization
import BEDC.Real.RatNumLogEnclosure

set_option maxHeartbeats 2000000

namespace BEDC.Derived.RHRoute.FiniteEulerDirichlet

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Derived.RHRoute.FinitePrimeWindow
open BEDC.Derived.RHRoute.HalfPlaneEulerProduct
open BEDC.Real.RatNumKernel
open BEDC.Real.RatNumLogEnclosure

abbrev Rat : Type :=
  HalfPlaneEulerProduct.Rat

abbrev RatComplex : Type :=
  HalfPlaneEulerProduct.RatComplex

abbrev NatOneLocal : BHist :=
  BHist.e1 BHist.Empty

def unitComplex : RatComplex :=
  { re := ratOne, im := ratZero }

structure QPrimeLocated
    (p : Nat) (hp : IsPrime p) (s : RatComplex) (h : HP1WitnessRat s) where
  envelope : LocatedComplexMagnitudeEnvelope
  envelope_eq : envelope = qPrimeSymbolicUnitEnvelope p hp s h
  radius_contracts : LocalSchurContractive p hp s h
  abs_lt_one : ratLt envelope.absUB ratOne

def qPrime_located
    (p : Nat) (hp : IsPrime p) (s : RatComplex) (h : HP1WitnessRat s) :
    QPrimeLocated p hp s h :=
  { envelope := qPrimeSymbolicUnitEnvelope p hp s h
    envelope_eq := rfl
    radius_contracts := qPrime_localSchurContractive p hp s h
    abs_lt_one := qPrime_symbolicEnvelope_lt_one p hp s h }

structure SinglePrimeGeomLocated
    (p : Nat) (hp : IsPrime p) (s : RatComplex) (h : HP1WitnessRat s) where
  located : QPrimeLocated p hp s h
  partial_geom : Nat -> Rat
  partial_geom_eq :
    ∀ K : Nat, partial_geom K = qPrimeGeomSum p hp s h K
  factor_bound : Rat
  partial_le_factor_bound :
    ∀ K : Nat, ratLe (partial_geom K) factor_bound

def singlePrimeGeomLocated
    (p : Nat) (hp : IsPrime p) (s : RatComplex) (h : HP1WitnessRat s) :
    SinglePrimeGeomLocated p hp s h :=
  { located := qPrime_located p hp s h
    partial_geom := qPrimeGeomSum p hp s h
    partial_geom_eq := fun _K => rfl
    factor_bound := (primeEulerFactorBounded p hp s h).factor_bound
    partial_le_factor_bound :=
      fun K => qPrime_geomSum_le_factor_bound p hp s h K }

inductive EulerDirichletObligationKind where
  | singlePrimeInfiniteGeomInverse
  | primeExponentReadbackFromPermutation
  | finiteWindowEffectiveFubini
  | infiniteEulerToZetaEffectiveConvergence

structure EffectiveConvergenceObligation where
  kind : EulerDirichletObligationKind
  modulus_request : Nat -> Nat

def singlePrimeInfiniteGeomObligation
    (p : Nat) (_hp : IsPrime p) (_s : RatComplex) (_h : HP1WitnessRat _s) :
    EffectiveConvergenceObligation :=
  { kind := EulerDirichletObligationKind.singlePrimeInfiniteGeomInverse
    modulus_request := fun precision => precision + p }

def infiniteEulerZetaConvergenceObligation :
    EffectiveConvergenceObligation :=
  { kind := EulerDirichletObligationKind.infiniteEulerToZetaEffectiveConvergence
    modulus_request := fun precision => precision }

def exponentSpine : List (Nat × Nat) -> List BHist
  | [] => []
  | (p, e) :: rest =>
      List.replicate e (natToUnary p) ++ exponentSpine rest

private theorem list_append_nil_clean {α : Type u} :
    ∀ xs : List α, xs ++ [] = xs
  | [] => rfl
  | x :: xs => congrArg (List.cons x) (list_append_nil_clean xs)

private theorem list_append_assoc_clean {α : Type u} :
    ∀ xs ys zs : List α, (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
  | [], _ys, _zs => rfl
  | x :: xs, ys, zs =>
      congrArg (List.cons x) (list_append_assoc_clean xs ys zs)

private theorem mem_append_elim_clean {α : Type u} {x : α} :
    ∀ xs ys : List α, x ∈ xs ++ ys -> x ∈ xs ∨ x ∈ ys
  | [], _ys, hmem => Or.inr hmem
  | a :: xs, ys, hmem => by
      cases hmem with
      | head => exact Or.inl (List.Mem.head xs)
      | tail _ tailMem =>
          cases mem_append_elim_clean xs ys tailMem with
          | inl left => exact Or.inl (List.Mem.tail a left)
          | inr right => exact Or.inr right

private theorem mem_replicate_eq_clean {α : Type u} (a x : α) :
    ∀ n : Nat, x ∈ List.replicate n a -> x = a
  | 0, hmem => by cases hmem
  | Nat.succ n, hmem => by
      cases hmem with
      | head => rfl
      | tail _ tailMem => exact mem_replicate_eq_clean a x n tailMem

def encNat (xs : List (Nat × Nat)) : Nat :=
  BEDC.Derived.PrimeUp.primeFlatProductNat (exponentSpine xs)

def enc (xs : List (Nat × Nat)) : BHist :=
  BEDC.Derived.PrimeUp.primePowerProduct (exponentSpine xs)

theorem exponentSpine_all_prime :
    ∀ {xs : List (Nat × Nat)},
      (∀ p e, (p, e) ∈ xs -> IsPrime p) ->
        ∀ q : BHist, q ∈ exponentSpine xs -> NatPrime q
  | [], hprime, q, hmem => by
      cases hmem
  | (p, e) :: rest, hprime, q, hmem => by
      unfold exponentSpine at hmem
      cases mem_append_elim_clean
          (List.replicate e (natToUnary p)) (exponentSpine rest) hmem with
      | inl inRep =>
          have qEq : q = natToUnary p :=
            mem_replicate_eq_clean (natToUnary p) q e inRep
          cases qEq
          exact hprime p e (List.Mem.head rest)
      | inr inRest =>
          exact exponentSpine_all_prime
            (fun p' e' member => hprime p' e' (List.Mem.tail (p, e) member))
            q inRest

theorem exponentSpine_product :
    ∀ xs : List (Nat × Nat),
      (∀ p e, (p, e) ∈ xs -> IsPrime p) ->
        PrimeFactorizationProduct (exponentSpine xs) (enc xs)
  | [], _hprime => by
      unfold enc exponentSpine BEDC.Derived.PrimeUp.primePowerProduct
      change hsame (natToUnary 1) NatOneLocal
      exact (NatUp_unary_standard_bridge.right.right.right.left
        (natToUnary_unary 1) (unary_e1_closed unary_empty)).mpr (by
          rw [natToUnary_length]
          exact (NatUp_unary_standard_bridge.right.left BHist.Empty unary_empty).symm)
  | (p, e) :: rest, hprime => by
      unfold enc
      have primeEvery :
          ∀ q : BHist, q ∈ exponentSpine ((p, e) :: rest) -> NatPrime q :=
        exponentSpine_all_prime hprime
      have productPrime :
          ∀ entries : List BHist,
            (∀ q : BHist, q ∈ entries -> NatPrime q) ->
              PrimeFactorizationProduct entries
                (BEDC.Derived.PrimeUp.primePowerProduct entries) := by
        intro entries allPrime
        induction entries with
        | nil =>
            unfold BEDC.Derived.PrimeUp.primePowerProduct
            change hsame (natToUnary 1) NatOneLocal
            exact (NatUp_unary_standard_bridge.right.right.right.left
              (natToUnary_unary 1) (unary_e1_closed unary_empty)).mpr (by
                rw [natToUnary_length]
                exact (NatUp_unary_standard_bridge.right.left BHist.Empty unary_empty).symm)
        | cons q qs ih =>
            have qPrime : NatPrime q := allPrime q (List.Mem.head qs)
            have tailProduct :=
              ih (fun r member => allPrime r (List.Mem.tail q member))
            have qUnary : UnaryHistory q := qPrime.left
            have tailUnary :
                UnaryHistory (BEDC.Derived.PrimeUp.primePowerProduct qs) :=
              BEDC.Derived.PrimeUp.primePowerProduct_unary qs
            cases NatMul_total qUnary tailUnary with
            | intro raw rawData =>
                have sameRaw :
                    hsame raw
                      (BEDC.Derived.PrimeUp.primePowerProduct (q :: qs)) := by
                  have lenRaw : bwordLength raw = bwordLength q *
                      bwordLength (BEDC.Derived.PrimeUp.primePowerProduct qs) :=
                    NatMul_bwordLength rawData.right
                  apply (NatUp_unary_standard_bridge.right.right.right.left
                    rawData.left
                    (BEDC.Derived.PrimeUp.primePowerProduct_unary (q :: qs))).mpr
                  unfold BEDC.Derived.PrimeUp.primePowerProduct
                  rw [natToUnary_length]
                  rw [BEDC.Derived.PrimeUp.primePowerProductNat_eq_flat]
                  unfold BEDC.Derived.PrimeUp.primeFlatProductNat
                  rw [lenRaw]
                  unfold BEDC.Derived.PrimeUp.primePowerProduct at tailUnary
                  have tailLen :
                      bwordLength
                          (BEDC.Derived.PrimeUp.primePowerProduct qs) =
                        BEDC.Derived.PrimeUp.primeFlatProductNat qs := by
                    unfold BEDC.Derived.PrimeUp.primePowerProduct
                    rw [natToUnary_length]
                    exact BEDC.Derived.PrimeUp.primePowerProductNat_eq_flat qs
                  rw [tailLen]
                exact ⟨qPrime,
                  BEDC.Derived.PrimeUp.primePowerProduct qs,
                  tailProduct,
                  (NatMul_result_hsame_transport rawData.right sameRaw).right⟩
      exact productPrime (exponentSpine ((p, e) :: rest)) primeEvery

theorem factorization_enc_same
    {xs ys : List (Nat × Nat)}
    (hxs : ∀ p e, (p, e) ∈ xs -> IsPrime p)
    (hys : ∀ p e, (p, e) ∈ ys -> IsPrime p)
    (same : hsame (enc xs) (enc ys)) :
    ListPermPrime (exponentSpine xs) (exponentSpine ys) := by
  have leftProduct : PrimeFactorizationProduct (exponentSpine xs) (enc xs) :=
    exponentSpine_product xs hxs
  have rightProductAtLeft :
      PrimeFactorizationProduct (exponentSpine ys) (enc xs) :=
    PrimeFactorizationProduct_result_hsame_transport
      (exponentSpine_product ys hys) (hsame_symm same)
  exact factorization_unique_perm leftProduct rightProductAtLeft

def histCount (needle : BHist) : List BHist -> Nat
  | [] => 0
  | x :: xs =>
      if x = needle then Nat.succ (histCount needle xs)
      else histCount needle xs

theorem histCount_append (needle : BHist) :
    ∀ xs ys : List BHist,
      histCount needle (xs ++ ys) =
        histCount needle xs + histCount needle ys
  | [], ys => (Nat.zero_add (histCount needle ys)).symm
  | x :: xs, ys => by
      change
        (if x = needle then Nat.succ (histCount needle (xs ++ ys))
          else histCount needle (xs ++ ys)) =
        (if x = needle then Nat.succ (histCount needle xs)
          else histCount needle xs) + histCount needle ys
      by_cases hx : x = needle
      · rw [if_pos hx, if_pos hx, histCount_append needle xs ys, Nat.succ_add]
      · rw [if_neg hx, if_neg hx, histCount_append needle xs ys]

theorem histCount_replicate_same (needle : BHist) :
    ∀ e : Nat, histCount needle (List.replicate e needle) = e
  | 0 => rfl
  | Nat.succ e => by
      change
        (if needle = needle then
            Nat.succ (histCount needle (List.replicate e needle))
          else histCount needle (List.replicate e needle)) = Nat.succ e
      rw [if_pos rfl, histCount_replicate_same needle e]

theorem histCount_replicate_ne {needle entry : BHist}
    (hne : entry ≠ needle) :
    ∀ e : Nat, histCount needle (List.replicate e entry) = 0
  | 0 => rfl
  | Nat.succ e => by
      change
        (if entry = needle then
            Nat.succ (histCount needle (List.replicate e entry))
          else histCount needle (List.replicate e entry)) = 0
      rw [if_neg hne, histCount_replicate_ne hne e]

theorem histCount_perm {needle : BHist} {xs ys : List BHist} :
    ListPermPrime xs ys -> histCount needle xs = histCount needle ys := by
  intro perm
  induction perm with
  | nil => rfl
  | cons x _perm ih =>
      change
        (if x = needle then Nat.succ (histCount needle _)
          else histCount needle _) =
        (if x = needle then Nat.succ (histCount needle _)
          else histCount needle _)
      by_cases hx : x = needle
      · rw [if_pos hx, if_pos hx, ih]
      · rw [if_neg hx, if_neg hx, ih]
  | swap x y l =>
      change
        (if y = needle then Nat.succ (histCount needle (x :: l))
          else histCount needle (x :: l)) =
        (if x = needle then Nat.succ (histCount needle (y :: l))
          else histCount needle (y :: l))
      by_cases hx : x = needle
      · by_cases hy : y = needle
        · rw [if_pos hx, if_pos hy]
          change
            Nat.succ
                (if x = needle then Nat.succ (histCount needle l)
                  else histCount needle l) =
              Nat.succ
                (if y = needle then Nat.succ (histCount needle l)
                  else histCount needle l)
          rw [if_pos hx, if_pos hy]
        · rw [if_pos hx, if_neg hy]
          change
            (if x = needle then Nat.succ (histCount needle l)
              else histCount needle l) =
              Nat.succ
                (if y = needle then Nat.succ (histCount needle l)
                  else histCount needle l)
          rw [if_pos hx, if_neg hy]
      · by_cases hy : y = needle
        · rw [if_neg hx, if_pos hy]
          change
            Nat.succ
                (if x = needle then Nat.succ (histCount needle l)
                  else histCount needle l) =
              (if y = needle then Nat.succ (histCount needle l)
                else histCount needle l)
          rw [if_neg hx, if_pos hy]
        · rw [if_neg hx, if_neg hy]
          change
            (if x = needle then Nat.succ (histCount needle l)
              else histCount needle l) =
              (if y = needle then Nat.succ (histCount needle l)
                else histCount needle l)
          rw [if_neg hx, if_neg hy]
  | trans _p _q ihp ihq =>
      exact Eq.trans ihp ihq

theorem natToUnary_injective {m n : Nat} :
    natToUnary m = natToUnary n -> m = n := by
  intro same
  have lengthSame :
      bwordLength (natToUnary m) = bwordLength (natToUnary n) :=
    congrArg bwordLength same
  rw [natToUnary_length, natToUnary_length] at lengthSame
  exact lengthSame

def exponentVector (primes : List Nat) (exponents : List Nat) :
    List (Nat × Nat) :=
  match primes, exponents with
  | [], _ => []
  | _p :: _ps, [] => []
  | p :: ps, e :: es => (p, e) :: exponentVector ps es

theorem exponentVector_all_prime :
    ∀ {primes exponents : List Nat},
      All IsPrime primes ->
        ∀ p e, (p, e) ∈ exponentVector primes exponents -> IsPrime p
  | [], _exponents, _allPrime, p, e, member => by
      cases member
  | _p :: _ps, [], _allPrime, p, e, member => by
      cases member
  | p0 :: ps, _e0 :: es, allPrime, p, e, member => by
      cases allPrime with
      | cons p0Prime psPrime =>
          cases member with
          | head => exact p0Prime
          | tail _ tailMember =>
              exact exponentVector_all_prime psPrime p e tailMember

theorem histCount_exponentSpine_absent :
    ∀ {primes exponents : List Nat} {target : Nat},
      target ∉ primes ->
        histCount (natToUnary target)
          (exponentSpine (exponentVector primes exponents)) = 0
  | [], _exponents, _target, _absent => rfl
  | _p :: _ps, [], _target, _absent => rfl
  | p :: ps, e :: es, target, absent => by
      change
        histCount (natToUnary target)
          (List.replicate e (natToUnary p) ++
            exponentSpine (exponentVector ps es)) = 0
      rw [histCount_append]
      have pNeTarget : p ≠ target := by
        intro same
        exact absent (same ▸ List.Mem.head ps)
      have histNe : natToUnary p ≠ natToUnary target := by
        intro sameUnary
        exact pNeTarget (natToUnary_injective sameUnary)
      have tailAbsent : target ∉ ps := by
        intro member
        exact absent (List.Mem.tail p member)
      rw [histCount_replicate_ne histNe]
      rw [histCount_exponentSpine_absent
        (primes := ps) (exponents := es) tailAbsent]

theorem histCount_exponentSpine_head :
    ∀ {p : Nat} {ps es : List Nat} {e : Nat},
      p ∉ ps ->
        histCount (natToUnary p)
          (exponentSpine (exponentVector (p :: ps) (e :: es))) = e
  | p, ps, es, e, absent => by
      change
        histCount (natToUnary p)
          (List.replicate e (natToUnary p) ++
            exponentSpine (exponentVector ps es)) = e
      rw [histCount_append]
      rw [histCount_replicate_same]
      rw [histCount_exponentSpine_absent
        (primes := ps) (exponents := es) absent]
      exact Nat.add_zero e

theorem histCount_exponentSpine_cons_tail
    {p q e : Nat} {ps es : List Nat} :
    q ∈ ps -> p ∉ ps ->
      histCount (natToUnary q)
        (exponentSpine (exponentVector (p :: ps) (e :: es))) =
      histCount (natToUnary q)
        (exponentSpine (exponentVector ps es)) := by
  intro qMem pAbsent
  change
    histCount (natToUnary q)
      (List.replicate e (natToUnary p) ++
        exponentSpine (exponentVector ps es)) =
    histCount (natToUnary q) (exponentSpine (exponentVector ps es))
  rw [histCount_append]
  have pNeQ : p ≠ q := by
    intro same
    exact pAbsent (same ▸ qMem)
  have histNe : natToUnary p ≠ natToUnary q := by
    intro sameUnary
    exact pNeQ (natToUnary_injective sameUnary)
  rw [histCount_replicate_ne histNe]
  exact Nat.zero_add _

theorem exponents_unique_of_spine_counts :
    ∀ {primes left right : List Nat},
      NoDup primes -> left.length = primes.length ->
        right.length = primes.length ->
          (∀ p, p ∈ primes ->
            histCount (natToUnary p)
              (exponentSpine (exponentVector primes left)) =
            histCount (natToUnary p)
              (exponentSpine (exponentVector primes right))) ->
            left = right
  | [], left, right, _nodup, leftLen, rightLen, _counts => by
      cases left with
      | nil =>
          cases right with
          | nil => rfl
          | cons _r _rs => cases rightLen
      | cons _l _ls => cases leftLen
  | p :: ps, left, right, nodup, leftLen, rightLen, counts => by
      cases left with
      | nil => cases leftLen
      | cons le les =>
          cases right with
          | nil => cases rightLen
          | cons re res =>
              cases nodup with
              | cons pAbsent psNodup =>
                  have tailLeftLen : les.length = ps.length :=
                    Nat.succ.inj leftLen
                  have tailRightLen : res.length = ps.length :=
                    Nat.succ.inj rightLen
                  have pCount := counts p (List.Mem.head ps)
                  have leftHead :=
                    histCount_exponentSpine_head (p := p) (ps := ps)
                      (es := les) (e := le) pAbsent
                  have rightHead :=
                    histCount_exponentSpine_head (p := p) (ps := ps)
                      (es := res) (e := re) pAbsent
                  have headEq : le = re := by
                    rw [leftHead, rightHead] at pCount
                    exact pCount
                  cases headEq
                  have tailCounts :
                      ∀ q, q ∈ ps ->
                        histCount (natToUnary q)
                          (exponentSpine (exponentVector ps les)) =
                        histCount (natToUnary q)
                          (exponentSpine (exponentVector ps res)) := by
                    intro q qMem
                    have full := counts q (List.Mem.tail p qMem)
                    have leftTail :=
                      histCount_exponentSpine_cons_tail
                        (p := p) (q := q) (e := le) (ps := ps)
                        (es := les) qMem pAbsent
                    have rightTail :=
                      histCount_exponentSpine_cons_tail
                        (p := p) (q := q) (e := le) (ps := ps)
                        (es := res) qMem pAbsent
                    rw [leftTail, rightTail] at full
                    exact full
                  have tailEq : les = res :=
                    exponents_unique_of_spine_counts psNodup
                      tailLeftLen tailRightLen tailCounts
                  cases tailEq
                  rfl

theorem encWindow_exponents_unique
    {primes left right : List Nat}
    (nodup : NoDup primes) (allPrime : All IsPrime primes)
    (leftLen : left.length = primes.length)
    (rightLen : right.length = primes.length)
    (same : hsame (enc (exponentVector primes left))
      (enc (exponentVector primes right))) :
    left = right := by
  have allLeftPrime :
      ∀ q e, (q, e) ∈ exponentVector primes left -> IsPrime q :=
    exponentVector_all_prime allPrime
  have allRightPrime :
      ∀ q e, (q, e) ∈ exponentVector primes right -> IsPrime q :=
    exponentVector_all_prime allPrime
  have perm := factorization_enc_same allLeftPrime allRightPrime same
  apply exponents_unique_of_spine_counts nodup leftLen rightLen
  intro p pMem
  exact histCount_perm (needle := natToUnary p) perm

structure FormalEulerTerm where
  encoded : BHist
  factors : List BHist
  factors_encode : hsame (primePowerProduct factors) encoded

def formalTermFromFactors (factors : List BHist) : FormalEulerTerm :=
  { encoded := primePowerProduct factors
    factors := factors
    factors_encode := hsame_refl _ }

def unitFormalTerm : FormalEulerTerm :=
  formalTermFromFactors []

def attachPrime (p : Nat) (term : FormalEulerTerm) : FormalEulerTerm :=
  formalTermFromFactors (natToUnary p :: term.factors)

def expandPrimePowers (p : Nat) : Nat -> List FormalEulerTerm
  | 0 => [unitFormalTerm]
  | Nat.succ K =>
      expandPrimePowers p K ++
        [formalTermFromFactors (List.replicate (Nat.succ K) (natToUnary p))]

def multiplyTerm (left right : FormalEulerTerm) : FormalEulerTerm :=
  formalTermFromFactors (left.factors ++ right.factors)

def multiplyByTerm (a : FormalEulerTerm) : List FormalEulerTerm -> List FormalEulerTerm
  | [] => []
  | b :: bs => multiplyTerm a b :: multiplyByTerm a bs

def distributeTerms : List FormalEulerTerm -> List FormalEulerTerm -> List FormalEulerTerm
  | [], _right => []
  | a :: as, right => multiplyByTerm a right ++ distributeTerms as right

def addPrimePowerToTerms (p e : Nat) : List FormalEulerTerm -> List FormalEulerTerm
  | [] => []
  | term :: terms =>
      formalTermFromFactors (List.replicate e (natToUnary p) ++ term.factors) ::
        addPrimePowerToTerms p e terms

def encodedTermsForPrime (p : Nat) : Nat -> List FormalEulerTerm -> List FormalEulerTerm
  | 0, terms => addPrimePowerToTerms p 0 terms
  | Nat.succ K, terms =>
      encodedTermsForPrime p K terms ++
        addPrimePowerToTerms p (Nat.succ K) terms

theorem multiplyByTerm_power_eq_addPrimePower
    (p e : Nat) :
    ∀ terms : List FormalEulerTerm,
      multiplyByTerm
          (formalTermFromFactors (List.replicate e (natToUnary p))) terms =
        addPrimePowerToTerms p e terms
  | [] => rfl
  | term :: terms => by
      change
        formalTermFromFactors (List.replicate e (natToUnary p) ++ term.factors) ::
            multiplyByTerm
              (formalTermFromFactors (List.replicate e (natToUnary p))) terms =
          formalTermFromFactors (List.replicate e (natToUnary p) ++ term.factors) ::
            addPrimePowerToTerms p e terms
      exact congrArg
        (fun tail =>
          formalTermFromFactors (List.replicate e (natToUnary p) ++ term.factors) ::
            tail)
        (multiplyByTerm_power_eq_addPrimePower p e terms)

theorem distributeTerms_singleton
    (term : FormalEulerTerm) (right : List FormalEulerTerm) :
    distributeTerms [term] right = multiplyByTerm term right := by
  change multiplyByTerm term right ++ [] = multiplyByTerm term right
  exact list_append_nil_clean (multiplyByTerm term right)

theorem distributeTerms_append_left
    (xs ys right : List FormalEulerTerm) :
    distributeTerms (xs ++ ys) right =
      distributeTerms xs right ++ distributeTerms ys right := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      change
        multiplyByTerm x right ++ distributeTerms (xs ++ ys) right =
          (multiplyByTerm x right ++ distributeTerms xs right) ++
            distributeTerms ys right
      rw [ih]
      exact (list_append_assoc_clean (multiplyByTerm x right)
        (distributeTerms xs right) (distributeTerms ys right)).symm

theorem distribute_expandPrimePowers_eq_encodedTermsForPrime
    (p K : Nat) (terms : List FormalEulerTerm) :
    distributeTerms (expandPrimePowers p K) terms =
      encodedTermsForPrime p K terms := by
  induction K with
  | zero =>
      change distributeTerms [unitFormalTerm] terms =
        addPrimePowerToTerms p 0 terms
      rw [distributeTerms_singleton]
      exact multiplyByTerm_power_eq_addPrimePower p 0 terms
  | succ K ih =>
      change
        distributeTerms
            (expandPrimePowers p K ++
              [formalTermFromFactors (List.replicate (Nat.succ K) (natToUnary p))])
            terms =
          encodedTermsForPrime p K terms ++
            addPrimePowerToTerms p (Nat.succ K) terms
      rw [distributeTerms_append_left, ih]
      rw [distributeTerms_singleton]
      exact congrArg (fun tail => encodedTermsForPrime p K terms ++ tail)
        (multiplyByTerm_power_eq_addPrimePower p (Nat.succ K) terms)

def eulerExpandTerms (window : List (Nat × Nat)) : List FormalEulerTerm :=
  match window with
  | [] => [unitFormalTerm]
  | (p, K) :: rest =>
      distributeTerms (expandPrimePowers p K)
        (eulerExpandTerms rest)

def encodedDirichletTerms (window : List (Nat × Nat)) : List FormalEulerTerm :=
  match window with
  | [] => [unitFormalTerm]
  | (p, K) :: rest =>
      encodedTermsForPrime p K (encodedDirichletTerms rest)

theorem finiteEuler_eq_encodedDirichlet
    (window : List (Nat × Nat)) :
    eulerExpandTerms window = encodedDirichletTerms window := by
  induction window with
  | nil =>
      rfl
  | cons head rest ih =>
      cases head with
      | mk p K =>
          change
            distributeTerms (expandPrimePowers p K) (eulerExpandTerms rest) =
              encodedTermsForPrime p K (encodedDirichletTerms rest)
          rw [ih]
          exact distribute_expandPrimePowers_eq_encodedTermsForPrime p K
            (encodedDirichletTerms rest)

structure FiniteEulerDirichletPacket
    (window : List (Nat × Nat)) (s : RatComplex) (h : HP1WitnessRat s) where
  qprime_located :
    ∀ p K, (p, K) ∈ window -> (hp : IsPrime p) ->
      QPrimeLocated p hp s h
  finite_terms : List FormalEulerTerm
  finite_terms_eq : finite_terms = encodedDirichletTerms window
  finite_euler_eq_dirichlet :
    eulerExpandTerms window = encodedDirichletTerms window
  infinite_convergence_obligation : EffectiveConvergenceObligation

def finiteEulerDirichletPacket
    (window : List (Nat × Nat)) (s : RatComplex)
    (h : HP1WitnessRat s)
    (_primeInWindow : ∀ p K, (p, K) ∈ window -> IsPrime p) :
    FiniteEulerDirichletPacket window s h :=
  { qprime_located := by
      intro p K member hp
      exact qPrime_located p hp s h
    finite_terms := encodedDirichletTerms window
    finite_terms_eq := rfl
    finite_euler_eq_dirichlet := finiteEuler_eq_encodedDirichlet window
    infinite_convergence_obligation := infiniteEulerZetaConvergenceObligation }

def toyWindowTwoThree : List (Nat × Nat) :=
  [(2, 1), (3, 1)]

theorem two_isPrime : IsPrime 2 := by
  change NatPrime (natToUnary 2)
  exact NatPrime_first_pair.left

theorem three_isPrime : IsPrime 3 := by
  change NatPrime (natToUnary 3)
  exact NatPrime_first_pair.right

theorem toyWindowTwoThree_all_prime :
    ∀ p K, (p, K) ∈ toyWindowTwoThree -> IsPrime p := by
  intro p K member
  unfold toyWindowTwoThree at member
  cases member with
  | head =>
      exact two_isPrime
  | tail _ tailMember =>
      cases tailMember with
      | head =>
          exact three_isPrime
      | tail _ emptyMember =>
          cases emptyMember

theorem toy_finiteEuler_eq_encodedDirichlet :
    eulerExpandTerms toyWindowTwoThree =
      encodedDirichletTerms toyWindowTwoThree := by
  exact finiteEuler_eq_encodedDirichlet toyWindowTwoThree

theorem toy_factorization_nonempty :
    (encodedDirichletTerms toyWindowTwoThree).length = 4 := by
  rfl

theorem toy_enc_unique_factorization :
    ListPermPrime (exponentSpine toyWindowTwoThree)
      (exponentSpine toyWindowTwoThree) := by
  exact factorization_enc_same toyWindowTwoThree_all_prime
    toyWindowTwoThree_all_prime (hsame_refl _)

theorem qprime_located_norm_bound
    (p : Nat) (hp : IsPrime p) (s : RatComplex) (h : HP1WitnessRat s) :
    ratLt (qPrime_located p hp s h).envelope.absUB ratOne := by
  exact (qPrime_located p hp s h).abs_lt_one

theorem single_prime_geom_formal_bound
    (p : Nat) (hp : IsPrime p) (s : RatComplex) (h : HP1WitnessRat s)
    (K : Nat) :
    ratLe ((singlePrimeGeomLocated p hp s h).partial_geom K)
      (singlePrimeGeomLocated p hp s h).factor_bound := by
  exact (singlePrimeGeomLocated p hp s h).partial_le_factor_bound K

end BEDC.Derived.RHRoute.FiniteEulerDirichlet
