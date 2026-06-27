import BEDC.Algebra.FiniteFold
import BEDC.Algebra.Rel.IntegerUp
import BEDC.Derived.DivisorFunctionUp
import BEDC.Derived.MobiusInversionUp

namespace BEDC.Derived.MertensFunctionUp

open BEDC.FKernel.Hist
open BEDC.Algebra.FiniteFold
open BEDC.Derived.ArithmeticFnUp
open BEDC.Derived.DivisorFunctionUp
open BEDC.Derived.IntUp
open BEDC.Derived.MobiusInversionUp
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.RationalUp

/- Mertens 在显式有限素因子列表前缀上导出。 -/

abbrev FactorizationPrefix := List (List BHist)

def integerRing :
    BEDC.Algebra.Rel.RelCommRing IntegerUp IntEq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

def mertens (window : FactorizationPrefix) : IntegerUp :=
  listSum integerRing (window.map mobiusFunction)

def mertensDirect (window : FactorizationPrefix) : IntegerUp :=
  integerUpListSum (window.map mobiusFunction)

def intNegOne : IntegerUp :=
  IntNeg intOne

def factorOne : List BHist :=
  []

def factorTwo : List BHist :=
  [NatTwo]

def factorThree : List BHist :=
  [NatThree]

def factorFour : List BHist :=
  [NatTwo, NatTwo]

def prefixOne : FactorizationPrefix :=
  [factorOne]

def prefixTwo : FactorizationPrefix :=
  [factorOne, factorTwo]

def prefixThree : FactorizationPrefix :=
  [factorOne, factorTwo, factorThree]

def prefixFour : FactorizationPrefix :=
  [factorOne, factorTwo, factorThree, factorFour]

def mertensFloorKernelSum (entries : List BHist) : IntegerUp :=
  dirichletConvolution mobiusFunction oneFunction entries

def mertensFloorKernelUnit : IntegerUp :=
  mertensFloorKernelSum []

def mertensFloorSum (window : FactorizationPrefix) : IntegerUp :=
  listSum integerRing (window.map mertensFloorKernelSum)

def NonemptyFactorList (entries : List BHist) : Prop :=
  ∃ p : BHist, ∃ rest : List BHist, entries = p :: rest

def mertensFloorSumOne : IntegerUp :=
  mertens prefixOne

def mertensFloorSumTwo : IntegerUp :=
  IntAdd (mertens prefixTwo) (mertens prefixOne)

def mertensFloorSumThree : IntegerUp :=
  IntAdd (mertens prefixThree)
    (IntAdd (mertens prefixOne) (mertens prefixOne))

private theorem int_eq_refl (x : IntegerUp) : IntEq x x :=
  IntEq_refl x

private theorem int_eq_symm {x y : IntegerUp} : IntEq x y -> IntEq y x :=
  IntEq_symm

private theorem int_eq_trans {x y z : IntegerUp} :
    IntEq x y -> IntEq y z -> IntEq x z :=
  IntEq_trans

private theorem int_add_congr {a a' b b' : IntegerUp} :
    IntEq a a' -> IntEq b b' ->
      IntEq (IntAdd a b) (IntAdd a' b') :=
  BEDC.Derived.RationalUp.IntAdd_respects

private theorem int_add_zero (x : IntegerUp) :
    IntEq (IntAdd x intZero) x :=
  BEDC.Derived.RationalUp.IntAdd_zero x

private theorem int_zero_add (x : IntegerUp) :
    IntEq (IntAdd intZero x) x :=
  BEDC.Derived.RationalUp.IntAdd_zero_left x

theorem mertens_direct_eq_finiteFold (window : FactorizationPrefix) :
    IntEq (mertens window) (mertensDirect window) := by
  unfold mertens mertensDirect
  induction window with
  | nil =>
      exact IntEq_refl intZero
  | cons entries rest ih =>
      change IntEq
        (IntAdd (mobiusFunction entries) (listSum integerRing (rest.map mobiusFunction)))
        (IntAdd (mobiusFunction entries) (integerUpListSum (rest.map mobiusFunction)))
      exact int_add_congr (int_eq_refl (mobiusFunction entries)) ih

theorem mertens_nil :
    IntEq (mertens []) intZero := by
  exact IntEq_refl intZero

theorem mertens_snoc (window : FactorizationPrefix) (entries : List BHist) :
    IntEq (mertens (window ++ [entries]))
      (IntAdd (mertens window) (mobiusFunction entries)) := by
  induction window with
  | nil =>
      change IntEq (IntAdd (mobiusFunction entries) intZero)
        (IntAdd intZero (mobiusFunction entries))
      exact int_eq_trans (int_add_zero (mobiusFunction entries))
        (int_eq_symm (int_zero_add (mobiusFunction entries)))
  | cons head tail ih =>
      change IntEq
        (IntAdd (mobiusFunction head) (mertens (tail ++ [entries])))
        (IntAdd (IntAdd (mobiusFunction head) (mertens tail))
          (mobiusFunction entries))
      have step :
          IntEq
            (IntAdd (mobiusFunction head) (mertens (tail ++ [entries])))
            (IntAdd (mobiusFunction head)
              (IntAdd (mertens tail) (mobiusFunction entries))) :=
        int_add_congr (int_eq_refl (mobiusFunction head)) ih
      exact int_eq_trans step
        (int_eq_symm (BEDC.Derived.RationalUp.IntAdd_assoc
          (mobiusFunction head) (mertens tail) (mobiusFunction entries)))

theorem mobius_factor_one :
    IntEq (mobiusFunction factorOne) intOne := by
  exact IntEq_refl intOne

theorem mobius_factor_two :
    IntEq (mobiusFunction factorTwo) intNegOne := by
  exact IntEq_refl intNegOne

theorem mobius_factor_three :
    IntEq (mobiusFunction factorThree) intNegOne := by
  exact IntEq_refl intNegOne

theorem mobius_factor_four :
    IntEq (mobiusFunction factorFour) intZero := by
  exact IntEq_refl intZero

theorem NatTwo_prime :
    NatPrime NatTwo := by
  unfold NatTwo NatOne
  exact NatPrime_first_pair.left

theorem NatThree_prime :
    NatPrime NatThree := by
  unfold NatThree NatTwo NatOne
  exact NatPrime_first_pair.right

theorem factor_two_prime_factorization :
    PrimeFactorization NatTwo factorTwo := by
  unfold factorTwo
  exact ⟨NatTwo_prime.left,
    ⟨NatTwo_prime, NatOne, hsame_refl NatOne,
      NatMul.succ (NatMul.zero NatTwo_prime.left)
        (BEDC.FKernel.Cont.cont_left_unit NatTwo)⟩⟩

theorem factor_three_prime_factorization :
    PrimeFactorization NatThree factorThree := by
  unfold factorThree
  exact ⟨NatThree_prime.left,
    ⟨NatThree_prime, NatOne, hsame_refl NatOne,
      NatMul.succ (NatMul.zero NatThree_prime.left)
        (BEDC.FKernel.Cont.cont_left_unit NatThree)⟩⟩

theorem mertens_one :
    IntEq (mertens prefixOne) intOne := by
  change IntEq (IntAdd intOne intZero) intOne
  exact int_add_zero intOne

theorem mertens_two :
    IntEq (mertens prefixTwo) intZero := by
  change IntEq (IntAdd intOne (IntAdd intNegOne intZero)) intZero
  have tail : IntEq (IntAdd intNegOne intZero) intNegOne :=
    int_add_zero intNegOne
  have collapse :
      IntEq (IntAdd intOne (IntAdd intNegOne intZero))
        (IntAdd intOne intNegOne) :=
    int_add_congr (int_eq_refl intOne) tail
  exact int_eq_trans collapse (BEDC.Derived.RationalUp.IntAdd_neg intOne)

theorem mertens_three :
    IntEq (mertens prefixThree) intNegOne := by
  change IntEq
    (IntAdd intOne (IntAdd intNegOne (IntAdd intNegOne intZero)))
    intNegOne
  have tail : IntEq (IntAdd intNegOne intZero) intNegOne :=
    int_add_zero intNegOne
  have removeTail :
      IntEq
        (IntAdd intOne (IntAdd intNegOne (IntAdd intNegOne intZero)))
        (IntAdd intOne (IntAdd intNegOne intNegOne)) :=
    int_add_congr (int_eq_refl intOne)
      (int_add_congr (int_eq_refl intNegOne) tail)
  have reassoc :
      IntEq (IntAdd intOne (IntAdd intNegOne intNegOne))
        (IntAdd (IntAdd intOne intNegOne) intNegOne) :=
    int_eq_symm (BEDC.Derived.RationalUp.IntAdd_assoc intOne intNegOne intNegOne)
  have cancelHead :
      IntEq (IntAdd (IntAdd intOne intNegOne) intNegOne)
        (IntAdd intZero intNegOne) :=
    int_add_congr (BEDC.Derived.RationalUp.IntAdd_neg intOne)
      (int_eq_refl intNegOne)
  exact int_eq_trans removeTail
    (int_eq_trans reassoc (int_eq_trans cancelHead (int_zero_add intNegOne)))

theorem mertens_four :
    IntEq (mertens prefixFour) intNegOne := by
  change IntEq
    (IntAdd intOne
      (IntAdd intNegOne (IntAdd intNegOne (IntAdd intZero intZero))))
    intNegOne
  have zeroTail : IntEq (IntAdd intZero intZero) intZero :=
    int_add_zero intZero
  have removeZero :
      IntEq
        (IntAdd intOne
          (IntAdd intNegOne (IntAdd intNegOne (IntAdd intZero intZero))))
        (IntAdd intOne (IntAdd intNegOne (IntAdd intNegOne intZero))) :=
    int_add_congr (int_eq_refl intOne)
      (int_add_congr (int_eq_refl intNegOne)
        (int_add_congr (int_eq_refl intNegOne) zeroTail))
  exact int_eq_trans removeZero mertens_three

theorem mertens_floor_kernel_identity (entries : List BHist) :
    IntEq (mertensFloorKernelSum entries) (epsilonFunction entries) :=
  mobiusDirichletUnit entries

private theorem epsilon_nonempty {p : BHist} {rest : List BHist} :
    IntEq (epsilonFunction (p :: rest)) intZero := by
  exact IntEq_refl intZero

private theorem mertens_floor_sum_tail_zero :
    ∀ tail : FactorizationPrefix,
      (∀ entries : List BHist, entries ∈ tail -> NonemptyFactorList entries) ->
        IntEq (listSum integerRing (tail.map mertensFloorKernelSum)) intZero
  | [], _allNonempty =>
      IntEq_refl intZero
  | entries :: rest, allNonempty => by
      change IntEq
        (IntAdd (mertensFloorKernelSum entries)
          (listSum integerRing (rest.map mertensFloorKernelSum)))
        intZero
      have entriesNonempty : NonemptyFactorList entries :=
        allNonempty entries (List.Mem.head rest)
      have headZero : IntEq (mertensFloorKernelSum entries) intZero := by
        cases entriesNonempty with
        | intro p data =>
            cases data with
            | intro restEntries same =>
                cases same
                exact int_eq_trans (mertens_floor_kernel_identity (p :: restEntries))
                  epsilon_nonempty
      have tailZero :
          IntEq (listSum integerRing (rest.map mertensFloorKernelSum)) intZero :=
        mertens_floor_sum_tail_zero rest
          (fun row mem => allNonempty row (List.Mem.tail entries mem))
      have bothZero :
          IntEq
            (IntAdd (mertensFloorKernelSum entries)
              (listSum integerRing (rest.map mertensFloorKernelSum)))
            (IntAdd intZero intZero) :=
        int_add_congr headZero tailZero
      exact int_eq_trans bothZero (int_add_zero intZero)

theorem mertens_floor_kernel_unit_identity :
    IntEq mertensFloorKernelUnit intOne := by
  exact mertens_floor_kernel_identity []

theorem mertens_floor_sum_identity (tail : FactorizationPrefix) :
    (∀ entries : List BHist, entries ∈ tail -> NonemptyFactorList entries) ->
      IntEq (mertensFloorSum (factorOne :: tail)) intOne := by
  intro allNonempty
  unfold mertensFloorSum factorOne
  change IntEq
    (IntAdd (mertensFloorKernelSum [])
      (listSum integerRing (tail.map mertensFloorKernelSum)))
    intOne
  have headOne : IntEq (mertensFloorKernelSum []) intOne :=
    mertens_floor_kernel_identity []
  have tailZero :
      IntEq (listSum integerRing (tail.map mertensFloorKernelSum)) intZero :=
    mertens_floor_sum_tail_zero tail allNonempty
  have normalized :
      IntEq
        (IntAdd (mertensFloorKernelSum [])
          (listSum integerRing (tail.map mertensFloorKernelSum)))
        (IntAdd intOne intZero) :=
    int_add_congr headOne tailZero
  exact int_eq_trans normalized (int_add_zero intOne)

theorem mertens_floor_sum_one :
    IntEq mertensFloorSumOne intOne :=
  mertens_one

theorem mertens_floor_sum_two :
    IntEq mertensFloorSumTwo intOne := by
  unfold mertensFloorSumTwo
  have reduceLeft :
      IntEq (IntAdd (mertens prefixTwo) (mertens prefixOne))
        (IntAdd intZero intOne) :=
    int_add_congr mertens_two mertens_one
  exact int_eq_trans reduceLeft (int_zero_add intOne)

theorem mertens_floor_sum_three :
    IntEq mertensFloorSumThree intOne := by
  unfold mertensFloorSumThree
  have reducePieces :
      IntEq
        (IntAdd (mertens prefixThree)
          (IntAdd (mertens prefixOne) (mertens prefixOne)))
        (IntAdd intNegOne (IntAdd intOne intOne)) :=
    int_add_congr mertens_three
      (int_add_congr mertens_one mertens_one)
  have reassoc :
      IntEq (IntAdd intNegOne (IntAdd intOne intOne))
        (IntAdd (IntAdd intNegOne intOne) intOne) :=
    int_eq_symm (BEDC.Derived.RationalUp.IntAdd_assoc intNegOne intOne intOne)
  have cancel :
      IntEq (IntAdd (IntAdd intNegOne intOne) intOne)
        (IntAdd intZero intOne) :=
    int_add_congr (BEDC.Derived.RationalUp.IntAdd_neg_left intOne)
      (int_eq_refl intOne)
  exact int_eq_trans reducePieces
    (int_eq_trans reassoc (int_eq_trans cancel (int_zero_add intOne)))

theorem divisor_count_one_for_mertens :
    DivisorCountOfFactorization BEDC.Derived.PadicUp.NatOne
      BEDC.Derived.PadicUp.NatOne :=
  divisorCount_one

theorem divisor_count_two_for_mertens :
    DivisorCountOfFactorization NatTwo NatTwo :=
  divisorCount_single_prime_value NatTwo_prime

theorem divisor_count_three_for_mertens :
    DivisorCountOfFactorization NatThree NatTwo :=
  divisorCount_single_prime_value NatThree_prime

end BEDC.Derived.MertensFunctionUp
