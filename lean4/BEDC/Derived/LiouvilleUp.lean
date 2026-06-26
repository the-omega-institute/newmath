import BEDC.Derived.MobiusInversionUp
import BEDC.Algebra.Rel.IntegerUp

namespace BEDC.Derived.LiouvilleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ArithmeticFnUp
open BEDC.Derived.IntUp
open BEDC.Derived.MobiusInversionUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.RationalUp

def omegaFactorsNat (entries : List BHist) : Nat :=
  entries.length

def natEvenBool : Nat -> Bool
  | 0 => true
  | 1 => false
  | n + 2 => natEvenBool n

def liouvilleFactorsIntegerUp : List BHist -> IntegerUp
  | [] => intOne
  | _p :: ps => IntNeg (liouvilleFactorsIntegerUp ps)

def liouvilleFunction : ArithmeticFunction :=
  liouvilleFactorsIntegerUp

def liouvilleFactorListSum : List (List BHist) -> IntegerUp
  | [] => intZero
  | fs :: fss => IntAdd (liouvilleFactorsIntegerUp fs) (liouvilleFactorListSum fss)

def liouvilleDivisorSumFactors (entries : List BHist) : IntegerUp :=
  liouvilleFactorListSum (divisorFactorLists entries)

def squareIndicatorAux : List BHist -> List BHist -> IntegerUp
  | _seen, [] => intOne
  | seen, p :: ps =>
      if listContainsPrime p seen then squareIndicatorAux seen ps
      else
        if natEvenBool (listPrimeCountNat p ps + 1) then
          squareIndicatorAux (p :: seen) ps
        else intZero

def squareIndicatorIntegerUp (entries : List BHist) : IntegerUp :=
  squareIndicatorAux [] entries

def squareIndicatorFunction : ArithmeticFunction :=
  squareIndicatorIntegerUp

def LiouvilleValueOfFactorization (n : BHist) (value : IntegerUp) : Prop :=
  ∃ entries : List BHist,
    PrimeFactorization n entries ∧ IntEq value (liouvilleFactorsIntegerUp entries)

def SquareIndicatorOfFactorization (n : BHist) (indicator : IntegerUp) : Prop :=
  ∃ entries : List BHist,
    PrimeFactorization n entries ∧ IntEq indicator (squareIndicatorIntegerUp entries)

private def zring : BEDC.Algebra.Rel.RelCommRing IntegerUp IntEq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

private theorem zEq_refl (x : IntegerUp) : IntEq x x :=
  IntEq_refl x

private theorem zEq_symm {x y : IntegerUp} : IntEq x y -> IntEq y x :=
  IntEq_symm

private theorem zEq_trans {x y z : IntegerUp} :
    IntEq x y -> IntEq y z -> IntEq x z :=
  IntEq_trans

private theorem zAdd_respects {a a' b b' : IntegerUp} :
    IntEq a a' -> IntEq b b' ->
      IntEq (IntAdd a b) (IntAdd a' b') :=
  BEDC.Derived.RationalUp.IntAdd_respects

private theorem zMul_respects {a a' b b' : IntegerUp} :
    IntEq a a' -> IntEq b b' ->
      IntEq (IntMul a b) (IntMul a' b') :=
  BEDC.Derived.RationalUp.IntMul_respects

private theorem zNeg_respects {a b : IntegerUp} :
    IntEq a b -> IntEq (IntNeg a) (IntNeg b) :=
  BEDC.Derived.RationalUp.IntNeg_respects

private theorem zAdd_zero (a : IntegerUp) :
    IntEq (IntAdd a intZero) a :=
  BEDC.Derived.RationalUp.IntAdd_zero a

private theorem zZero_add (a : IntegerUp) :
    IntEq (IntAdd intZero a) a :=
  IntAdd_zero_left a

private theorem zAdd_neg (a : IntegerUp) :
    IntEq (IntAdd a (IntNeg a)) intZero :=
  BEDC.Derived.RationalUp.IntAdd_neg a

private theorem zNeg_zero :
    IntEq (IntNeg intZero) intZero :=
  zring.neg_zero

private theorem zNeg_add_pair (a b : IntegerUp) :
    IntEq (IntNeg (IntAdd a b)) (IntAdd (IntNeg a) (IntNeg b)) := by
  have hzero :
      IntEq (IntAdd (IntAdd a b) (IntAdd (IntNeg a) (IntNeg b))) intZero := by
    exact zEq_trans (zring.add_assoc a b (IntAdd (IntNeg a) (IntNeg b)))
      (zEq_trans
        (zring.add_congr (zEq_refl a)
          (zring.symm (zring.add_assoc b (IntNeg a) (IntNeg b))))
        (zEq_trans
          (zring.add_congr (zEq_refl a)
            (zring.add_congr (zring.add_comm b (IntNeg a))
              (zEq_refl (IntNeg b))))
          (zEq_trans
            (zring.add_congr (zEq_refl a)
              (zring.add_assoc (IntNeg a) b (IntNeg b)))
            (zEq_trans
              (zring.symm (zring.add_assoc a (IntNeg a)
                (IntAdd b (IntNeg b))))
              (zEq_trans
                (zring.add_congr (zAdd_neg a) (zAdd_neg b))
                (zZero_add intZero))))))
  exact zring.symm
    (zring.eq_neg_of_add_eq_zero (a := IntAdd a b)
      (b := IntAdd (IntNeg a) (IntNeg b)) hzero)

private theorem natEvenBool_succ (n : Nat) :
    natEvenBool (n + 1) = !natEvenBool n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change natEvenBool n = !natEvenBool (n + 1)
      rw [ih]
      cases natEvenBool n <;> rfl

private theorem list_map_map_local {α β γ : Type}
    (f : α -> β) (g : β -> γ) :
    ∀ xs : List α, (xs.map f).map g = xs.map (fun x => g (f x)) := by
  intro xs
  induction xs with
  | nil =>
      rfl
  | cons x rest ih =>
      change g (f x) :: (rest.map f).map g =
        g (f x) :: rest.map (fun y => g (f y))
      exact congrArg (fun tail => g (f x) :: tail) ih

theorem omegaFactorsNat_length (entries : List BHist) :
    omegaFactorsNat entries = entries.length := by
  rfl

theorem liouvilleFactorsIntegerUp_omega_nil :
    liouvilleFactorsIntegerUp [] = intOne := by
  rfl

theorem liouvilleFactorsIntegerUp_omega_cons
    (p : BHist) (ps : List BHist) :
    liouvilleFactorsIntegerUp (p :: ps) =
      IntNeg (liouvilleFactorsIntegerUp ps) := by
  rfl

theorem liouvilleFactors_append_multiplicative
    (xs ys : List BHist) :
    IntEq (liouvilleFactorsIntegerUp (xs ++ ys))
      (IntMul (liouvilleFactorsIntegerUp xs) (liouvilleFactorsIntegerUp ys)) := by
  induction xs with
  | nil =>
      change IntEq (liouvilleFactorsIntegerUp ys)
        (IntMul intOne (liouvilleFactorsIntegerUp ys))
      exact zEq_symm (IntMul_one_left (liouvilleFactorsIntegerUp ys))
  | cons p ps ih =>
      change IntEq (IntNeg (liouvilleFactorsIntegerUp (ps ++ ys)))
        (IntMul (IntNeg (liouvilleFactorsIntegerUp ps))
          (liouvilleFactorsIntegerUp ys))
      have negIH :
          IntEq (IntNeg (liouvilleFactorsIntegerUp (ps ++ ys)))
            (IntNeg (IntMul (liouvilleFactorsIntegerUp ps)
              (liouvilleFactorsIntegerUp ys))) :=
        zNeg_respects ih
      have negMul :
          IntEq
            (IntMul (IntNeg (liouvilleFactorsIntegerUp ps))
              (liouvilleFactorsIntegerUp ys))
            (IntNeg (IntMul (liouvilleFactorsIntegerUp ps)
              (liouvilleFactorsIntegerUp ys))) :=
        BEDC.Algebra.Rel.IntegerUp_neg_mul
          (liouvilleFactorsIntegerUp ps) (liouvilleFactorsIntegerUp ys)
      exact zEq_trans negIH (zEq_symm negMul)

theorem liouville_function_append_multiplicative
    (xs ys : List BHist) :
    IntEq (liouvilleFunction (xs ++ ys))
      (IntMul (liouvilleFunction xs) (liouvilleFunction ys)) :=
  liouvilleFactors_append_multiplicative xs ys

theorem liouville_completely_multiplicative_of_products
    {m n mn : BHist} {xs ys : List BHist} :
    PrimeFactorizationProduct xs m ->
      PrimeFactorizationProduct ys n ->
        NatMul m n mn ->
          LiouvilleValueOfFactorization mn
            (IntMul (liouvilleFactorsIntegerUp xs)
              (liouvilleFactorsIntegerUp ys)) := by
  intro fx fy mul
  have product :
      PrimeFactorizationProduct (xs ++ ys) mn :=
    PrimeFactorizationProduct_append_mul fx fy mul
  exact ⟨xs ++ ys,
    ⟨NatMul_result_unary (PrimeFactorizationProduct_result_unary fx) mul,
      product⟩,
    zEq_symm (liouvilleFactors_append_multiplicative xs ys)⟩

theorem liouville_completely_multiplicative_of_factorizations
    {m n mn : BHist} {xs ys : List BHist} :
    PrimeFactorization m xs ->
      PrimeFactorization n ys ->
        NatMul m n mn ->
          LiouvilleValueOfFactorization mn
            (IntMul (liouvilleFactorsIntegerUp xs)
              (liouvilleFactorsIntegerUp ys)) := by
  intro fx fy mul
  exact liouville_completely_multiplicative_of_products fx.right fy.right mul

private theorem liouvilleFactorListSum_append
    (xs ys : List (List BHist)) :
    IntEq (liouvilleFactorListSum (xs ++ ys))
      (IntAdd (liouvilleFactorListSum xs) (liouvilleFactorListSum ys)) := by
  induction xs with
  | nil =>
      change IntEq (liouvilleFactorListSum ys)
        (IntAdd intZero (liouvilleFactorListSum ys))
      exact zEq_symm (zZero_add (liouvilleFactorListSum ys))
  | cons fs fss ih =>
      change IntEq
        (IntAdd (liouvilleFactorsIntegerUp fs)
          (liouvilleFactorListSum (fss ++ ys)))
        (IntAdd
          (IntAdd (liouvilleFactorsIntegerUp fs) (liouvilleFactorListSum fss))
          (liouvilleFactorListSum ys))
      have inner :
          IntEq
            (IntAdd (liouvilleFactorsIntegerUp fs)
              (liouvilleFactorListSum (fss ++ ys)))
            (IntAdd (liouvilleFactorsIntegerUp fs)
              (IntAdd (liouvilleFactorListSum fss)
                (liouvilleFactorListSum ys))) :=
        zAdd_respects (zEq_refl (liouvilleFactorsIntegerUp fs)) ih
      exact zEq_trans inner
        (zEq_symm (BEDC.Derived.RationalUp.IntAdd_assoc (liouvilleFactorsIntegerUp fs)
          (liouvilleFactorListSum fss) (liouvilleFactorListSum ys)))

private theorem liouvilleFactorListSum_all_zero :
    ∀ factorLists : List (List BHist),
      (∀ fs : List BHist, fs ∈ factorLists ->
        IntEq (liouvilleFactorsIntegerUp fs) intZero) ->
        IntEq (liouvilleFactorListSum factorLists) intZero := by
  intro factorLists
  induction factorLists with
  | nil =>
      intro _allZero
      exact IntEq_refl intZero
  | cons fs fss ih =>
      intro allZero
      change IntEq
        (IntAdd (liouvilleFactorsIntegerUp fs) (liouvilleFactorListSum fss))
        intZero
      have headZero : IntEq (liouvilleFactorsIntegerUp fs) intZero :=
        allZero fs (show fs ∈ fs :: fss from List.mem_cons_self)
      have tailZero : IntEq (liouvilleFactorListSum fss) intZero :=
        ih (fun gs mem => allZero gs (List.mem_cons_of_mem fs mem))
      have addZero :
          IntEq
            (IntAdd (liouvilleFactorsIntegerUp fs) (liouvilleFactorListSum fss))
            (IntAdd intZero intZero) :=
        zAdd_respects headZero tailZero
      exact zEq_trans addZero (zZero_add intZero)

private theorem liouvilleFactorListSum_map_cons_neg
    (p : BHist) :
    ∀ xs : List (List BHist),
      IntEq (liouvilleFactorListSum (xs.map (fun fs => p :: fs)))
        (IntNeg (liouvilleFactorListSum xs)) := by
  intro xs
  induction xs with
  | nil =>
      change IntEq intZero (IntNeg intZero)
      exact zEq_symm zNeg_zero
  | cons fs fss ih =>
      change IntEq
        (IntAdd (IntNeg (liouvilleFactorsIntegerUp fs))
          (liouvilleFactorListSum (fss.map (fun fs => p :: fs))))
        (IntNeg
          (IntAdd (liouvilleFactorsIntegerUp fs)
            (liouvilleFactorListSum fss)))
      have left :
          IntEq
            (IntAdd (IntNeg (liouvilleFactorsIntegerUp fs))
              (liouvilleFactorListSum (fss.map (fun fs => p :: fs))))
            (IntAdd (IntNeg (liouvilleFactorsIntegerUp fs))
              (IntNeg (liouvilleFactorListSum fss))) :=
        zAdd_respects (zEq_refl _) ih
      exact zEq_trans left
        (zEq_symm (zNeg_add_pair (liouvilleFactorsIntegerUp fs)
          (liouvilleFactorListSum fss)))

private theorem liouvillePrimePowerAppendBlock
    (p : BHist) (rest : List BHist) :
    ∀ n : Nat,
      IntEq
        (liouvilleFactorListSum
          ((primePowerFactorLists p n).map (fun fs => fs ++ rest)))
        (if natEvenBool n then liouvilleFactorsIntegerUp rest else intZero) := by
  intro n
  induction n with
  | zero =>
      change IntEq (IntAdd (liouvilleFactorsIntegerUp rest) intZero)
        (liouvilleFactorsIntegerUp rest)
      exact zAdd_zero (liouvilleFactorsIntegerUp rest)
  | succ n ih =>
      unfold primePowerFactorLists
      change IntEq
        (IntAdd (liouvilleFactorsIntegerUp rest)
          (liouvilleFactorListSum
            (((primePowerFactorLists p n).map (fun fs => p :: fs)).map
              (fun fs => fs ++ rest))))
        (if natEvenBool (n + 1) then liouvilleFactorsIntegerUp rest else intZero)
      rw [list_map_map_local (fun fs : List BHist => p :: fs)
        (fun fs : List BHist => fs ++ rest)]
      change IntEq
        (IntAdd (liouvilleFactorsIntegerUp rest)
          (liouvilleFactorListSum
            ((primePowerFactorLists p n).map
              (fun fs => p :: (fs ++ rest)))))
        (if natEvenBool (n + 1) then liouvilleFactorsIntegerUp rest else intZero)
      have tailNeg :
          IntEq
            (liouvilleFactorListSum
              ((primePowerFactorLists p n).map
                (fun fs => p :: (fs ++ rest))))
            (IntNeg
              (liouvilleFactorListSum
                ((primePowerFactorLists p n).map
                  (fun fs => fs ++ rest)))) := by
        simpa [list_map_map_local (fun fs : List BHist => fs ++ rest)
          (fun fs : List BHist => p :: fs)]
          using liouvilleFactorListSum_map_cons_neg p
            ((primePowerFactorLists p n).map (fun fs => fs ++ rest))
      cases evenN : natEvenBool n
      · have nextEven : natEvenBool (n + 1) = true := by
          rw [natEvenBool_succ n, evenN]
          rfl
        rw [nextEven]
        have prevZero :
            IntEq
              (liouvilleFactorListSum
                ((primePowerFactorLists p n).map (fun fs => fs ++ rest)))
              intZero := by
          rw [evenN] at ih
          exact ih
        have tailZero :
            IntEq
              (liouvilleFactorListSum
                ((primePowerFactorLists p n).map
                  (fun fs => p :: (fs ++ rest))))
              intZero :=
          zEq_trans tailNeg
            (zEq_trans (zNeg_respects prevZero) zNeg_zero)
        exact zEq_trans
          (zAdd_respects (zEq_refl (liouvilleFactorsIntegerUp rest)) tailZero)
          (zAdd_zero (liouvilleFactorsIntegerUp rest))
      · have nextOdd : natEvenBool (n + 1) = false := by
          rw [natEvenBool_succ n, evenN]
          rfl
        rw [nextOdd]
        have prevValue :
            IntEq
              (liouvilleFactorListSum
                ((primePowerFactorLists p n).map (fun fs => fs ++ rest)))
              (liouvilleFactorsIntegerUp rest) := by
          rw [evenN] at ih
          exact ih
        have tailNegValue :
            IntEq
              (liouvilleFactorListSum
                ((primePowerFactorLists p n).map
                  (fun fs => p :: (fs ++ rest))))
              (IntNeg (liouvilleFactorsIntegerUp rest)) :=
          zEq_trans tailNeg (zNeg_respects prevValue)
        exact zEq_trans
          (zAdd_respects (zEq_refl (liouvilleFactorsIntegerUp rest)) tailNegValue)
          (zAdd_neg (liouvilleFactorsIntegerUp rest))

private theorem liouvilleFactorListSum_appendFactorListProducts_even
    (left right : List (List BHist)) :
    (∀ rest : List BHist, rest ∈ right ->
      IntEq (liouvilleFactorListSum (left.map (fun l => l ++ rest)))
        (liouvilleFactorsIntegerUp rest)) ->
      IntEq (liouvilleFactorListSum (appendFactorListProducts left right))
        (liouvilleFactorListSum right) := by
  intro blockValue
  induction right with
  | nil =>
      exact IntEq_refl intZero
  | cons rest rests ih =>
      unfold appendFactorListProducts
      have split :
          IntEq
            (liouvilleFactorListSum
              ((left.map (fun l => l ++ rest)) ++
                appendFactorListProducts left rests))
            (IntAdd
              (liouvilleFactorListSum (left.map (fun l => l ++ rest)))
              (liouvilleFactorListSum (appendFactorListProducts left rests))) :=
        liouvilleFactorListSum_append (left.map (fun l => l ++ rest))
          (appendFactorListProducts left rests)
      have headValue :
          IntEq (liouvilleFactorListSum (left.map (fun l => l ++ rest)))
            (liouvilleFactorsIntegerUp rest) :=
        blockValue rest (show rest ∈ rest :: rests from List.mem_cons_self)
      have tailValue :
          IntEq (liouvilleFactorListSum (appendFactorListProducts left rests))
            (liouvilleFactorListSum rests) :=
        ih (fun r mem => blockValue r (List.mem_cons_of_mem rest mem))
      exact zEq_trans split (zAdd_respects headValue tailValue)

private theorem liouvilleFactorListSum_appendFactorListProducts_zero
    (left right : List (List BHist)) :
    (∀ rest : List BHist, rest ∈ right ->
      IntEq (liouvilleFactorListSum (left.map (fun l => l ++ rest))) intZero) ->
      IntEq (liouvilleFactorListSum (appendFactorListProducts left right))
        intZero := by
  intro blockZero
  induction right with
  | nil =>
      exact IntEq_refl intZero
  | cons rest rests ih =>
      unfold appendFactorListProducts
      have split :
          IntEq
            (liouvilleFactorListSum
              ((left.map (fun l => l ++ rest)) ++
                appendFactorListProducts left rests))
            (IntAdd
              (liouvilleFactorListSum (left.map (fun l => l ++ rest)))
              (liouvilleFactorListSum (appendFactorListProducts left rests))) :=
        liouvilleFactorListSum_append (left.map (fun l => l ++ rest))
          (appendFactorListProducts left rests)
      have headZero :
          IntEq (liouvilleFactorListSum (left.map (fun l => l ++ rest)))
            intZero :=
        blockZero rest (show rest ∈ rest :: rests from List.mem_cons_self)
      have tailZero :
          IntEq (liouvilleFactorListSum (appendFactorListProducts left rests))
            intZero :=
        ih (fun r mem => blockZero r (List.mem_cons_of_mem rest mem))
      exact zEq_trans split
        (zEq_trans (zAdd_respects headZero tailZero) (zZero_add intZero))

private theorem sum_liouville_divisorFactorListsAux_eq_squareIndicatorAux
    (seen entries : List BHist) :
    IntEq (liouvilleFactorListSum (divisorFactorListsAux seen entries))
      (squareIndicatorAux seen entries) := by
  induction entries generalizing seen with
  | nil =>
      change IntEq (IntAdd intOne intZero) intOne
      exact zAdd_zero intOne
  | cons p ps ih =>
      unfold divisorFactorListsAux squareIndicatorAux
      cases seenHas : listContainsPrime p seen
      · change IntEq
          (liouvilleFactorListSum
            (appendFactorListProducts
              (primePowerFactorLists p (listPrimeCountNat p ps + 1))
              (divisorFactorListsAux (p :: seen) ps)))
          (if natEvenBool (listPrimeCountNat p ps + 1) then
            squareIndicatorAux (p :: seen) ps
          else intZero)
        cases evenExp : natEvenBool (listPrimeCountNat p ps + 1)
        · change IntEq
            (liouvilleFactorListSum
              (appendFactorListProducts
                (primePowerFactorLists p (listPrimeCountNat p ps + 1))
                (divisorFactorListsAux (p :: seen) ps)))
            intZero
          exact liouvilleFactorListSum_appendFactorListProducts_zero
            (primePowerFactorLists p (listPrimeCountNat p ps + 1))
            (divisorFactorListsAux (p :: seen) ps)
            (fun rest _mem => by
              have block :=
                liouvillePrimePowerAppendBlock p rest
                  (listPrimeCountNat p ps + 1)
              rw [evenExp] at block
              exact block)
        · change IntEq
            (liouvilleFactorListSum
              (appendFactorListProducts
                (primePowerFactorLists p (listPrimeCountNat p ps + 1))
                (divisorFactorListsAux (p :: seen) ps)))
            (squareIndicatorAux (p :: seen) ps)
          have reduced :
              IntEq
                (liouvilleFactorListSum
                  (appendFactorListProducts
                    (primePowerFactorLists p (listPrimeCountNat p ps + 1))
                    (divisorFactorListsAux (p :: seen) ps)))
                (liouvilleFactorListSum
                  (divisorFactorListsAux (p :: seen) ps)) :=
            liouvilleFactorListSum_appendFactorListProducts_even
              (primePowerFactorLists p (listPrimeCountNat p ps + 1))
              (divisorFactorListsAux (p :: seen) ps)
              (fun rest _mem => by
                have block :=
                  liouvillePrimePowerAppendBlock p rest
                    (listPrimeCountNat p ps + 1)
                rw [evenExp] at block
                exact block)
          exact zEq_trans reduced (ih (p :: seen))
      · exact ih seen

theorem sum_liouville_eq_squareIndicator (entries : List BHist) :
    IntEq (liouvilleDivisorSumFactors entries)
      (squareIndicatorIntegerUp entries) := by
  unfold liouvilleDivisorSumFactors squareIndicatorIntegerUp divisorFactorLists
  exact sum_liouville_divisorFactorListsAux_eq_squareIndicatorAux [] entries

theorem liouvilleDivisorSum_eq_squareIndicator_of_factorization
    {n : BHist} {entries : List BHist} :
    PrimeFactorization n entries ->
      IntEq (liouvilleDivisorSumFactors entries)
        (squareIndicatorIntegerUp entries) := by
  intro _factorization
  exact sum_liouville_eq_squareIndicator entries

theorem squareIndicator_of_factorization_from_liouville_sum
    {n : BHist} {entries : List BHist} :
    PrimeFactorization n entries ->
      SquareIndicatorOfFactorization n
        (liouvilleDivisorSumFactors entries) := by
  intro factorization
  exact ⟨entries, factorization, sum_liouville_eq_squareIndicator entries⟩

private theorem integerUpListSum_liouville_one_over_splits
    (splits : List (List BHist × List BHist)) :
    IntEq
      (integerUpListSum
        (splits.map (fun split =>
          IntMul (liouvilleFunction split.1) (oneFunction split.2))))
      (liouvilleFactorListSum (splitLefts splits)) := by
  induction splits with
  | nil =>
      exact IntEq_refl intZero
  | cons split splits ih =>
      have head :
          IntEq (IntMul (liouvilleFunction split.1) (oneFunction split.2))
            (liouvilleFactorsIntegerUp split.1) := by
        unfold liouvilleFunction oneFunction
        exact BEDC.Derived.RationalUp.IntMul_one (liouvilleFactorsIntegerUp split.1)
      exact zAdd_respects head ih

theorem liouvilleDirichletSquareIndicator (entries : List BHist) :
    IntEq (dirichletConvolution liouvilleFunction oneFunction entries)
      (squareIndicatorFunction entries) := by
  unfold dirichletConvolution squareIndicatorFunction
  have splitSum :
      IntEq
        (integerUpListSum
          ((divisorFactorSplits entries).map
            (fun split => IntMul (liouvilleFunction split.1) (oneFunction split.2))))
        (liouvilleFactorListSum (splitLefts (divisorFactorSplits entries))) :=
    integerUpListSum_liouville_one_over_splits (divisorFactorSplits entries)
  have projected :
      IntEq (liouvilleFactorListSum (splitLefts (divisorFactorSplits entries)))
        (squareIndicatorIntegerUp entries) := by
    rw [divisorFactorSplits_lefts entries]
    exact sum_liouville_eq_squareIndicator entries
  exact zEq_trans splitSum projected

theorem liouvilleDirichletSquareIndicator_function :
    ArithmeticFnEq (dirichletConvolution liouvilleFunction oneFunction)
      squareIndicatorFunction := by
  intro entries
  exact liouvilleDirichletSquareIndicator entries

end BEDC.Derived.LiouvilleUp
