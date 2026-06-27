import BEDC.Derived.EulerTheoremUp
import BEDC.Derived.FermatLittleUp
import BEDC.Derived.PolyRootBoundUp
import BEDC.Derived.PrimeUp.DivisionWithRemainder
import BEDC.Derived.PrimeUp.NatMulTransport

namespace BEDC.Derived.PrimitiveRootUp

open BEDC.Algebra.Rel
open BEDC.Algebra.FiniteFold
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.NatUp
open BEDC.Derived.IntUp
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.ZModUp
open BEDC.Derived.ZModFieldUp
open BEDC.Derived.ZModResidueList
open BEDC.Derived.EulerTheoremUp
open BEDC.Derived.FermatWilsonUp
open BEDC.Derived.PolyRootBoundUp

variable {A : Type u} {r : A -> A -> Prop}

private theorem relPow_add (R : RelCommRing A r) (a : A) :
    ∀ m n : Nat,
      r (relPow R a (m + n)) (R.mul (relPow R a m) (relPow R a n)) := by
  intro m n
  induction n with
  | zero =>
      change r (relPow R a m) (R.mul (relPow R a m) R.one)
      exact R.symm (R.mul_one (relPow R a m))
  | succ n ih =>
      change r (R.mul (relPow R a (m + n)) a)
        (R.mul (relPow R a m) (R.mul (relPow R a n) a))
      exact R.trans
        (R.mul_congr ih (R.refl a))
        (R.mul_assoc (relPow R a m) (relPow R a n) a)

private theorem relPow_mul_period (R : RelCommRing A r) (a : A) {k : Nat} :
    r (relPow R a k) R.one ->
      ∀ q : Nat, r (relPow R a (k * q)) R.one := by
  intro period q
  induction q with
  | zero =>
      change r R.one R.one
      exact R.refl R.one
  | succ q ih =>
      rw [Nat.mul_succ]
      exact R.trans
        (relPow_add R a (k * q) k)
        (R.trans
          (R.mul_congr ih period)
          (R.one_mul R.one))

private theorem relPow_drop_period_prefix
    (R : RelCommRing A r) (a : A) {k : Nat} :
    r (relPow R a k) R.one ->
      ∀ q rest : Nat,
        r (relPow R a (k * q + rest)) (relPow R a rest) := by
  intro period q rest
  exact R.trans
    (relPow_add R a (k * q) rest)
    (R.trans
      (R.mul_congr (relPow_mul_period R a period q) (R.refl (relPow R a rest)))
      (R.one_mul (relPow R a rest)))

private theorem unary_nonempty_length_positive {h : BHist} :
    UnaryHistory h -> (h = BHist.Empty -> False) -> 0 < bwordLength h := by
  intro hUnary hNonempty
  cases h with
  | Empty =>
      exact False.elim (hNonempty rfl)
  | e0 h =>
      cases hUnary
  | e1 h =>
      change 0 < Nat.succ (bwordLength h)
      exact Nat.succ_pos (bwordLength h)

private theorem NatUnaryStrictPrefix_length_lt {r k : BHist} :
    UnaryHistory k -> NatUnaryStrictPrefix r k -> bwordLength r < bwordLength k := by
  intro kUnary strict
  cases strict with
  | intro tail tailData =>
      have rUnary : UnaryHistory r :=
        unary_cont_left_factor tailData.right.right kUnary
      have tailPositive : 0 < bwordLength tail :=
        unary_nonempty_length_positive tailData.left tailData.right.left
      have lengthK :
          bwordLength k = bwordLength r + bwordLength tail :=
        NatUp_unary_standard_bridge.right.right.right.right rUnary
          tailData.left tailData.right.right
      rw [lengthK]
      exact Nat.lt_add_of_pos_right tailPositive

def PowerOneAtNat
    (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (a : ZMod n) (k : Nat) : Prop :=
  zmodEq (zmodPowByNat n nUnary nNonempty a k)
    (zmodOne n nUnary nNonempty)

def monomialCoeffs {p : BHist} (prime : NatPrime p) : Nat -> List (ZMod p)
  | 0 => [(zmodRing prime).one]
  | d + 1 => (zmodRing prime).zero :: monomialCoeffs prime d

def powSubOneCoeffs {p : BHist} (prime : NatPrime p) : Nat -> List (ZMod p)
  | 0 => [(zmodRing prime).zero]
  | d + 1 => (zmodRing prime).neg (zmodRing prime).one :: monomialCoeffs prime d

theorem monomialCoeffs_degree_exact {p : BHist} (prime : NatPrime p) :
    ∀ d : Nat, PolyDegreeExact prime (monomialCoeffs prime d) d
  | 0 =>
      polyDegreeExact_constant prime (zmodOne_nonzero prime)
  | d + 1 =>
      polyDegreeExact_step prime (monomialCoeffs_degree_exact prime d)

theorem powSubOneCoeffs_degree_exact_positive {p : BHist}
    (prime : NatPrime p) (d : Nat) :
    PolyDegreeExact prime (powSubOneCoeffs prime (d + 1)) (d + 1) := by
  change PolyDegreeExact prime
    ((zmodRing prime).neg (zmodRing prime).one :: monomialCoeffs prime d)
    (d + 1)
  exact polyDegreeExact_step prime (monomialCoeffs_degree_exact prime d)

private theorem monomialCoeffs_eval {p : BHist} (prime : NatPrime p)
    (x : ZMod p) :
    ∀ d : Nat,
      zmodEq (polyEval prime (monomialCoeffs prime d) x)
        (zmodPowByNat p prime.left (NatPrime_empty_absurd prime) x d)
  | 0 =>
      polyEval_singleton prime (zmodRing prime).one x
  | d + 1 => by
      let R := zmodRing prime
      have tail :
          zmodEq (polyEval prime (monomialCoeffs prime d) x)
            (zmodPowByNat p prime.left (NatPrime_empty_absurd prime) x d) :=
        monomialCoeffs_eval prime x d
      change zmodEq
        (R.add R.zero (R.mul x (polyEval prime (monomialCoeffs prime d) x)))
        (R.mul (zmodPowByNat p prime.left (NatPrime_empty_absurd prime) x d) x)
      exact R.trans
        (R.trans
          (R.add_congr (R.refl R.zero) (R.mul_congr (R.refl x) tail))
          (R.zero_add (R.mul x
            (zmodPowByNat p prime.left (NatPrime_empty_absurd prime) x d))))
        (R.mul_comm x
          (zmodPowByNat p prime.left (NatPrime_empty_absurd prime) x d))

theorem powerOneAtNat_polyRoot {p : BHist} (prime : NatPrime p)
    (x : ZMod p) (d : Nat) :
    PowerOneAtNat p prime.left (NatPrime_empty_absurd prime) x (d + 1) ->
      PolyRoot prime (powSubOneCoeffs prime (d + 1)) x := by
  intro powOne
  let R := zmodRing prime
  have tail :
      zmodEq (polyEval prime (monomialCoeffs prime d) x)
        (zmodPowByNat p prime.left (NatPrime_empty_absurd prime) x d) :=
    monomialCoeffs_eval prime x d
  have evalToPow :
      zmodEq (polyEval prime (powSubOneCoeffs prime (d + 1)) x)
        (R.add (R.neg R.one)
          (zmodPowByNat p prime.left (NatPrime_empty_absurd prime) x (d + 1))) := by
    change zmodEq
      (R.add (R.neg R.one)
        (R.mul x (polyEval prime (monomialCoeffs prime d) x)))
      (R.add (R.neg R.one)
        (R.mul (zmodPowByNat p prime.left (NatPrime_empty_absurd prime) x d) x))
    exact R.add_congr (R.refl (R.neg R.one))
      (R.trans
        (R.mul_congr (R.refl x) tail)
        (R.mul_comm x
          (zmodPowByNat p prime.left (NatPrime_empty_absurd prime) x d)))
  exact R.trans evalToPow
    (R.trans
      (R.add_congr (R.refl (R.neg R.one)) powOne)
      (R.neg_add R.one))

theorem powerOneAtNat_root_bound_list {p : BHist} (prime : NatPrime p)
    {d : Nat} {roots : List (ZMod p)} :
    ListNoDup roots ->
      (∀ x : ZMod p, x ∈ roots ->
        PowerOneAtNat p prime.left (NatPrime_empty_absurd prime) x (d + 1)) ->
        roots.length <= d + 1 := by
  intro nodup allRoots
  exact polyRootBound_list prime
    (powSubOneCoeffs_degree_exact_positive prime d)
    nodup
    (fun x mem => powerOneAtNat_polyRoot prime x d (allRoots x mem))

private theorem zmodPowByNat_eq_zmodPowNat {p : BHist}
    (prime : NatPrime p) (a : ZMod p) :
    ∀ k : Nat,
      zmodEq
        (zmodPowByNat p prime.left (NatPrime_empty_absurd prime) a k)
        (zmodPowNat prime a k)
  | 0 =>
      rfl
  | k + 1 => by
      change zmodEq
        (zmodMul p prime.left (NatPrime_empty_absurd prime)
          (zmodPowByNat p prime.left (NatPrime_empty_absurd prime) a k) a)
        (zmodMul p prime.left (NatPrime_empty_absurd prime)
          (zmodPowNat prime a k) a)
      exact zmodMul_congr prime.left (NatPrime_empty_absurd prime)
        (zmodPowByNat_eq_zmodPowNat prime a k)
        (zmodEq_refl a)

theorem zmodPowNat_fermat_nonzero {p : BHist} (prime : NatPrime p)
    (a : ZMod p) :
    zmodNonzero a ->
      zmodEq (zmodPowNat prime a (bwordLength p - 1))
        (zmodOne p prime.left (NatPrime_empty_absurd prime)) := by
  intro aNonzero
  have perm :
      ListPerm
        (List.map (zmodUnitMul prime a aNonzero) (nonzeroResidues prime))
        (nonzeroResidues prime) :=
    mulByUnit_permutes prime a aNonzero
  have powAtList :
      zmodEq (zmodPowNat prime a (nonzeroResidues prime).length)
        (zmodOne p prime.left (NatPrime_empty_absurd prime)) :=
    fermat_unit_list_permutation prime a aNonzero
      (nonzeroResidues prime)
      (nonzeroResidues_all_nonzero prime)
      perm
  rw [BEDC.Derived.FermatLittleUp.nonzeroResidues_length prime] at powAtList
  exact powAtList

theorem powerOneAtNat_fermat_prime_minus_one {p : BHist}
    (prime : NatPrime p) (a : ZMod p) :
    zmodNonzero a ->
      PowerOneAtNat p prime.left (NatPrime_empty_absurd prime) a
        (bwordLength p - 1) := by
  intro aNonzero
  unfold PowerOneAtNat zmodPowByNat
  exact zmodEq_trans
    (zmodPowByNat_eq_zmodPowNat prime a (bwordLength p - 1))
    (zmodPowNat_fermat_nonzero prime a aNonzero)

private theorem unaryPred_length {p : BHist} :
    UnaryHistory p -> bwordLength (unaryPred p) = bwordLength p - 1 := by
  intro pUnary
  cases p with
  | Empty =>
      rfl
  | e0 _ =>
      cases pUnary
  | e1 _ =>
      rfl

structure HasMultOrder
    (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (a : ZMod n) (k : BHist) where
  k_unary : UnaryHistory k
  k_positive : 0 < bwordLength k
  pow_one : PowerOneAtNat n nUnary nNonempty a (bwordLength k)
  minimal :
    ∀ j : Nat, 0 < j -> j < bwordLength k ->
      PowerOneAtNat n nUnary nNonempty a j -> False

def IsPrimitiveRoot
    (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (phi : BHist) (g : ZMod n) : Prop :=
  HasMultOrder n nUnary nNonempty g phi

private def powEqOneBool
    (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (a : ZMod n) (k : Nat) : Bool :=
  if (zmodPowByNat n nUnary nNonempty a k).val =
      (zmodOne n nUnary nNonempty).val then true else false

private theorem powEqOneBool_true
    (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (a : ZMod n) (k : Nat) :
    powEqOneBool n nUnary nNonempty a k = true ->
      PowerOneAtNat n nUnary nNonempty a k := by
  intro hit
  unfold powEqOneBool at hit
  by_cases same :
      (zmodPowByNat n nUnary nNonempty a k).val =
        (zmodOne n nUnary nNonempty).val
  · unfold PowerOneAtNat zmodEq
    exact same
  · rw [if_neg same] at hit
    cases hit

private theorem powEqOneBool_false
    (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (a : ZMod n) (k : Nat) :
    powEqOneBool n nUnary nNonempty a k = false ->
      PowerOneAtNat n nUnary nNonempty a k -> False := by
  intro miss powOne
  unfold powEqOneBool at miss
  by_cases same :
      (zmodPowByNat n nUnary nNonempty a k).val =
        (zmodOne n nUnary nNonempty).val
  · rw [if_pos same] at miss
    cases miss
  · unfold PowerOneAtNat zmodEq at powOne
    exact same powOne

def multOrderSearchFrom
    (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (a : ZMod n) : Nat -> Nat -> Option Nat
  | _start, 0 => none
  | start, fuel + 1 =>
      if powEqOneBool n nUnary nNonempty a start then
        some start
      else
        multOrderSearchFrom n nUnary nNonempty a (start + 1) fuel

theorem multOrderSearchFrom_sound
    (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (a : ZMod n) :
    ∀ {start fuel k : Nat},
      multOrderSearchFrom n nUnary nNonempty a start fuel = some k ->
        PowerOneAtNat n nUnary nNonempty a k
  | _start, 0, _k, found => by
      unfold multOrderSearchFrom at found
      cases found
  | start, fuel + 1, _k, found => by
      unfold multOrderSearchFrom at found
      cases hit : powEqOneBool n nUnary nNonempty a start with
      | false =>
          rw [hit] at found
          exact multOrderSearchFrom_sound n nUnary nNonempty a found
      | true =>
          rw [hit] at found
          cases found
          exact powEqOneBool_true n nUnary nNonempty a start hit

theorem multOrderSearchFrom_lower_bound
    (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (a : ZMod n) :
    ∀ {start fuel k : Nat},
      multOrderSearchFrom n nUnary nNonempty a start fuel = some k ->
        start <= k
  | _start, 0, _k, found => by
      unfold multOrderSearchFrom at found
      cases found
  | start, fuel + 1, _k, found => by
      unfold multOrderSearchFrom at found
      cases hit : powEqOneBool n nUnary nNonempty a start with
      | false =>
          rw [hit] at found
          exact Nat.le_trans (Nat.le_succ start)
            (multOrderSearchFrom_lower_bound n nUnary nNonempty a found)
      | true =>
          rw [hit] at found
          cases found
          exact Nat.le_refl start

theorem multOrderSearchFrom_minimal
    (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (a : ZMod n) :
    ∀ {start fuel k j : Nat},
      multOrderSearchFrom n nUnary nNonempty a start fuel = some k ->
        start <= j -> j < k ->
          PowerOneAtNat n nUnary nNonempty a j -> False
  | _start, 0, _k, _j, found, _jLower, _jLt, _powOne => by
      unfold multOrderSearchFrom at found
      cases found
  | start, fuel + 1, _k, j, found, jLower, jLt, powOne => by
      unfold multOrderSearchFrom at found
      cases hit : powEqOneBool n nUnary nNonempty a start with
      | false =>
          rw [hit] at found
          by_cases sameJ : j = start
          · cases sameJ
            exact powEqOneBool_false n nUnary nNonempty a start hit powOne
          · have startLtJ : start < j :=
              Nat.lt_of_le_of_ne jLower (fun same => sameJ same.symm)
            exact multOrderSearchFrom_minimal n nUnary nNonempty a found
              (Nat.succ_le_of_lt startLtJ) jLt powOne
      | true =>
          rw [hit] at found
          cases found
          exact (Nat.not_lt_of_ge jLower) jLt

def multOrder
    (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (a : ZMod n) : BHist :=
  match multOrderSearchFrom n nUnary nNonempty a 1 (bwordLength n + 1) with
  | some k => natToUnary k
  | none => BHist.Empty

theorem multOrderSearchFrom_has_order
    (n : BHist) (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (a : ZMod n) {fuel k : Nat} :
    multOrderSearchFrom n nUnary nNonempty a 1 fuel = some k ->
      HasMultOrder n nUnary nNonempty a (natToUnary k) := by
  intro found
  refine
    { k_unary := natToUnary_unary k
      k_positive := ?_
      pow_one := ?_
      minimal := ?_ }
  · rw [natToUnary_length]
    exact multOrderSearchFrom_lower_bound n nUnary nNonempty a found
  · rw [natToUnary_length]
    exact multOrderSearchFrom_sound n nUnary nNonempty a found
  · intro j jPositive jLt powOne
    rw [natToUnary_length] at jLt
    exact multOrderSearchFrom_minimal n nUnary nNonempty a found
      (Nat.succ_le_of_lt jPositive) jLt powOne

def orderOf {p : BHist} (prime : NatPrime p) (a : ZMod p) : BHist :=
  match multOrderSearchFrom p prime.left (NatPrime_empty_absurd prime) a
      1 (nonzeroResidues prime).length with
  | some k => natToUnary k
  | none => BHist.Empty

theorem orderOf_has_order_of_found {p : BHist} (prime : NatPrime p)
    (a : ZMod p) {k : Nat} :
    multOrderSearchFrom p prime.left (NatPrime_empty_absurd prime) a
      1 (nonzeroResidues prime).length = some k ->
        HasMultOrder p prime.left (NatPrime_empty_absurd prime) a
          (orderOf prime a) := by
  intro found
  unfold orderOf
  rw [found]
  exact multOrderSearchFrom_has_order p prime.left
    (NatPrime_empty_absurd prime) a found

theorem orderOf_fuel_eq_prime_minus_one {p : BHist} (prime : NatPrime p) :
    (nonzeroResidues prime).length = bwordLength p - 1 :=
  BEDC.Derived.FermatLittleUp.nonzeroResidues_length prime

theorem multOrder_divides_phi
    {n k phi : BHist}
    (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (a : ZMod n)
    (order : HasMultOrder n nUnary nNonempty a k)
    (phiUnary : UnaryHistory phi)
    (phiPow : PowerOneAtNat n nUnary nNonempty a (bwordLength phi)) :
    NatDivides k phi := by
  let period : Nat := bwordLength k
  have kNonempty : hsame k BHist.Empty -> False := by
    intro same
    cases same
    exact Nat.not_lt_zero 0 order.k_positive
  have divrem : ∃ q : BHist, ∃ r : BHist, NatDivRem k phi q r :=
    divRem_exists order.k_unary phiUnary kNonempty
  cases divrem with
  | intro q qRest =>
  cases qRest with
  | intro remainder divremData =>
  cases divremData with
  | intro product productData =>
  have periodPow :
      zmodEq (zmodPowByNat n nUnary nNonempty a period)
        (zmodOne n nUnary nNonempty) := by
    unfold period
    exact order.pow_one
  have dropRemainder :
      zmodEq
        (zmodPowByNat n nUnary nNonempty a
          (period * bwordLength q + bwordLength remainder))
        (zmodPowByNat n nUnary nNonempty a (bwordLength remainder)) := by
    unfold zmodPowByNat at periodPow
    unfold zmodPowByNat
    exact relPow_drop_period_prefix
      (zmodRelCommRing n nUnary nNonempty) a periodPow
      (bwordLength q) (bwordLength remainder)
  have decomposition :
      period * bwordLength q + bwordLength remainder = bwordLength phi := by
    unfold period
    rw [← NatMul_bwordLength productData.left]
    exact (NatAdd_length productData.right.left).symm
  have sumPowOne :
      zmodEq
        (zmodPowByNat n nUnary nNonempty a
          (period * bwordLength q + bwordLength remainder))
        (zmodOne n nUnary nNonempty) := by
    have samePow :
        zmodEq
          (zmodPowByNat n nUnary nNonempty a
            (period * bwordLength q + bwordLength remainder))
          (zmodPowByNat n nUnary nNonempty a (bwordLength phi)) := by
      rw [decomposition]
      exact zmodEq_refl _
    exact zmodEq_trans samePow phiPow
  have remainderPow :
      PowerOneAtNat n nUnary nNonempty a (bwordLength remainder) := by
    unfold PowerOneAtNat
    exact zmodEq_trans (zmodEq_symm dropRemainder) sumPowOne
  have remainderEmpty : hsame remainder BHist.Empty := by
    cases remainder with
    | Empty =>
        rfl
    | e0 tail =>
        cases NatAdd_right_unary productData.right.left
    | e1 tail =>
        have remainderPositive : 0 < bwordLength (BHist.e1 tail) := by
          change 0 < Nat.succ (bwordLength tail)
          exact Nat.succ_pos (bwordLength tail)
        have remainderLt : bwordLength (BHist.e1 tail) < period := by
          unfold period
          exact NatUnaryStrictPrefix_length_lt order.k_unary productData.right.right
        exact False.elim
          (order.minimal (bwordLength (BHist.e1 tail))
            remainderPositive remainderLt remainderPow)
  have sameProductPhi : hsame product phi := by
    cases remainderEmpty
    exact hsame_symm
      (cont_deterministic productData.right.left.right.right
        (cont_right_unit product))
  have shiftedProduct :=
    NatMul_result_hsame_transport productData.left sameProductPhi
  exact ⟨q, NatMul_right_unary productData.left, shiftedProduct.right⟩

theorem hasMultOrder_divides_prime_minus_one
    {p k : BHist} (prime : NatPrime p) (a : ZMod p) :
    zmodNonzero a ->
      HasMultOrder p prime.left (NatPrime_empty_absurd prime) a k ->
        NatDivides k (unaryPred p) := by
  intro aNonzero order
  exact multOrder_divides_phi prime.left (NatPrime_empty_absurd prime)
    a order (unaryPred_unary prime.left)
    (by
      have fermatPow :
          PowerOneAtNat p prime.left (NatPrime_empty_absurd prime) a
            (bwordLength p - 1) :=
        powerOneAtNat_fermat_prime_minus_one prime a aNonzero
      rw [unaryPred_length prime.left]
      exact fermatPow)

theorem hasMultOrder_root_bound_list {p k : BHist} (prime : NatPrime p)
    {roots : List (ZMod p)} :
    0 < bwordLength k ->
      ListNoDup roots ->
        (∀ x : ZMod p, x ∈ roots ->
          HasMultOrder p prime.left (NatPrime_empty_absurd prime) x k) ->
          roots.length <= bwordLength k := by
  intro kPositive nodup allOrders
  cases hLen : bwordLength k with
  | zero =>
      have positiveZero : 0 < 0 := by
        rw [hLen] at kPositive
        exact kPositive
      exact False.elim (Nat.not_lt_zero 0 positiveZero)
  | succ d =>
      exact powerOneAtNat_root_bound_list prime nodup
        (fun x mem => by
          have order := allOrders x mem
          rw [← hLen]
          exact order.pow_one)

abbrev NatTwo : BHist := natToUnary 2
abbrev NatFour : BHist := natToUnary 4
abbrev NatFive : BHist := natToUnary 5

private def NatFive_nonempty : hsame NatFive BHist.Empty -> False := by
  intro empty
  unfold NatFive natToUnary at empty
  cases empty

def twoModFive : ZMod NatFive :=
  zmodFromNat NatFive (natToUnary_unary 5) NatFive_nonempty
    NatTwo (natToUnary_unary 2)

private theorem two_mod_five_not_pow_one_at_one :
    PowerOneAtNat NatFive (natToUnary_unary 5) NatFive_nonempty
      twoModFive 1 -> False := by
  intro pow
  unfold PowerOneAtNat zmodPowByNat twoModFive zmodFromNat zmodOne zmodEq at pow
  change hsame
    (natModFn NatFive (natMulFn NatOne NatTwo))
    (natModFn NatFive NatOne) at pow
  unfold NatFive NatTwo NatOne natToUnary natMulFn natModFn at pow
  cases pow

private theorem two_mod_five_not_pow_one_at_two :
    PowerOneAtNat NatFive (natToUnary_unary 5) NatFive_nonempty
      twoModFive 2 -> False := by
  intro pow
  unfold PowerOneAtNat zmodPowByNat twoModFive zmodFromNat zmodOne zmodEq at pow
  unfold NatFive NatTwo NatOne natToUnary natMulFn natModFn at pow
  cases pow

private theorem two_mod_five_not_pow_one_at_three :
    PowerOneAtNat NatFive (natToUnary_unary 5) NatFive_nonempty
      twoModFive 3 -> False := by
  intro pow
  unfold PowerOneAtNat zmodPowByNat twoModFive zmodFromNat zmodOne zmodEq at pow
  unfold NatFive NatTwo NatOne natToUnary natMulFn natModFn at pow
  cases pow

private theorem two_mod_five_minimal :
    ∀ j : Nat, 0 < j -> j < bwordLength NatFour ->
      PowerOneAtNat NatFive (natToUnary_unary 5) NatFive_nonempty
        twoModFive j -> False := by
  intro j jPositive jLt pow
  cases j with
  | zero =>
      exact Nat.not_lt_zero 0 jPositive
  | succ j1 =>
      cases j1 with
      | zero =>
          exact two_mod_five_not_pow_one_at_one pow
      | succ j2 =>
          cases j2 with
          | zero =>
              exact two_mod_five_not_pow_one_at_two pow
          | succ j3 =>
              cases j3 with
              | zero =>
                  exact two_mod_five_not_pow_one_at_three pow
              | succ j4 =>
                  change Nat.succ (Nat.succ (Nat.succ (Nat.succ j4))) < 4 at jLt
                  have ltThree :
                      Nat.succ (Nat.succ (Nat.succ j4)) < 3 :=
                    Nat.succ_lt_succ_iff.mp jLt
                  have ltTwo : Nat.succ (Nat.succ j4) < 2 :=
                    Nat.succ_lt_succ_iff.mp ltThree
                  have ltOne : Nat.succ j4 < 1 :=
                    Nat.succ_lt_succ_iff.mp ltTwo
                  have ltZero : j4 < 0 :=
                    Nat.succ_lt_succ_iff.mp ltOne
                  exact Nat.not_lt_zero j4 ltZero

theorem two_mod_five_has_order_four :
    HasMultOrder NatFive (natToUnary_unary 5) NatFive_nonempty
      twoModFive NatFour where
  k_unary := natToUnary_unary 4
  k_positive := by
    change 0 < 4
    exact Nat.succ_pos 3
  pow_one := by
    unfold PowerOneAtNat zmodPowByNat twoModFive zmodFromNat zmodOne zmodEq
    unfold NatFive NatTwo NatOne natToUnary natMulFn natModFn
    rfl
  minimal := two_mod_five_minimal

theorem two_mod_five_is_primitive_root :
    IsPrimitiveRoot NatFive (natToUnary_unary 5) NatFive_nonempty
      NatFour twoModFive :=
  two_mod_five_has_order_four

theorem two_mod_five_multOrder :
    hsame
      (multOrder NatFive (natToUnary_unary 5) NatFive_nonempty twoModFive)
      NatFour := by
  rfl

end BEDC.Derived.PrimitiveRootUp
