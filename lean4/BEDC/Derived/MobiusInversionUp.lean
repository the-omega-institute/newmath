import BEDC.Derived.ArithmeticFnUp
import BEDC.Derived.IntUp.CommRing
import BEDC.Derived.PadicUp.ExactDivision

namespace BEDC.Derived.MobiusInversionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ArithmeticFnUp
open BEDC.Derived.IntUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.RationalUp
open BEDC.Derived.PadicUp

abbrev ArithmeticFunction := List BHist -> IntegerUp

def oneFunction : ArithmeticFunction :=
  fun _entries => intOne

def epsilonFunction : ArithmeticFunction :=
  mobiusIndicatorIntegerUp

def mobiusFunction : ArithmeticFunction :=
  mobiusFactorsIntegerUp

def primePowerFactorSplits (p : BHist) : Nat -> List (List BHist × List BHist)
  | 0 => [([], [])]
  | k + 1 =>
      ([], repeatPrimeFactor p (k + 1)) ::
        (primePowerFactorSplits p k).map (fun split => (p :: split.1, split.2))

def appendFactorSplitProducts
    (left right : List (List BHist × List BHist)) :
    List (List BHist × List BHist) :=
  match right with
  | [] => []
  | r :: rs =>
      left.map (fun l => (l.1 ++ r.1, l.2 ++ r.2)) ++
        appendFactorSplitProducts left rs

def divisorFactorSplitsAux :
    List BHist -> List BHist -> List (List BHist × List BHist)
  | _seen, [] => [([], [])]
  | seen, p :: ps =>
      if listContainsPrime p seen then divisorFactorSplitsAux seen ps
      else appendFactorSplitProducts
        (primePowerFactorSplits p (listPrimeCountNat p ps + 1))
        (divisorFactorSplitsAux (p :: seen) ps)

def divisorFactorSplits (entries : List BHist) :
    List (List BHist × List BHist) :=
  divisorFactorSplitsAux [] entries

def splitLefts : List (List BHist × List BHist) -> List (List BHist)
  | [] => []
  | split :: splits => split.1 :: splitLefts splits

def splitRights : List (List BHist × List BHist) -> List (List BHist)
  | [] => []
  | split :: splits => split.2 :: splitRights splits

def dirichletConvolution (f g : ArithmeticFunction) : ArithmeticFunction :=
  fun entries =>
    integerUpListSum
      ((divisorFactorSplits entries).map
        (fun split => IntMul (f split.1) (g split.2)))

def ArithmeticFnEq (f g : ArithmeticFunction) : Prop :=
  forall entries : List BHist, IntEq (f entries) (g entries)

theorem natQuotFn_exact_for_divisor {D q n : BHist}
    (DUnary : UnaryHistory D)
    (DNonempty : hsame D BHist.Empty -> False)
    (qUnary : UnaryHistory q) :
    NatMul D q n -> hsame (natQuotFn D n) q :=
  natQuotFn_mul_exact DUnary DNonempty qUnary

private theorem splitLefts_append
    (xs ys : List (List BHist × List BHist)) :
    splitLefts (xs ++ ys) = splitLefts xs ++ splitLefts ys := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      change x.1 :: splitLefts (xs ++ ys) = x.1 :: splitLefts xs ++ splitLefts ys
      exact congrArg (fun tail => x.1 :: tail) ih

private theorem splitLefts_map_append_left
    (left : List (List BHist × List BHist)) (r : List BHist × List BHist) :
    splitLefts (left.map (fun l => (l.1 ++ r.1, l.2 ++ r.2))) =
      (splitLefts left).map (fun l => l ++ r.1) := by
  induction left with
  | nil =>
      rfl
  | cons l ls ih =>
      change (l.1 ++ r.1) :: splitLefts (ls.map
          (fun l => (l.1 ++ r.1, l.2 ++ r.2))) =
        (l.1 ++ r.1) :: (splitLefts ls).map (fun l => l ++ r.1)
      exact congrArg (fun tail => (l.1 ++ r.1) :: tail) ih

private theorem splitLefts_appendFactorSplitProducts
    (left right : List (List BHist × List BHist)) :
    splitLefts (appendFactorSplitProducts left right) =
      appendFactorListProducts (splitLefts left) (splitLefts right) := by
  induction right with
  | nil =>
      rfl
  | cons r rs ih =>
      unfold appendFactorSplitProducts appendFactorListProducts
      change splitLefts
          (left.map (fun l => (l.1 ++ r.1, l.2 ++ r.2)) ++
            appendFactorSplitProducts left rs) =
        (splitLefts left).map (fun l => l ++ r.1) ++
          appendFactorListProducts (splitLefts left) (splitLefts rs)
      rw [splitLefts_append, splitLefts_map_append_left, ih]

private theorem splitLefts_map_prime_cons
    (p : BHist) (splits : List (List BHist × List BHist)) :
    splitLefts (splits.map (fun split => (p :: split.1, split.2))) =
      (splitLefts splits).map (fun fs => p :: fs) := by
  induction splits with
  | nil =>
      rfl
  | cons split splits ih =>
      change (p :: split.1) ::
          splitLefts (splits.map (fun split => (p :: split.1, split.2))) =
        (p :: split.1) :: (splitLefts splits).map (fun fs => p :: fs)
      exact congrArg (fun tail => (p :: split.1) :: tail) ih

private theorem splitLefts_primePowerFactorSplits (p : BHist) :
    forall k : Nat,
      splitLefts (primePowerFactorSplits p k) = primePowerFactorLists p k
  | 0 =>
      rfl
  | k + 1 => by
      unfold primePowerFactorSplits primePowerFactorLists
      change [] :: splitLefts
          ((primePowerFactorSplits p k).map (fun split => (p :: split.1, split.2))) =
        [] :: (primePowerFactorLists p k).map (fun fs => p :: fs)
      rw [splitLefts_map_prime_cons, splitLefts_primePowerFactorSplits p k]

private theorem splitLefts_divisorFactorSplitsAux (seen entries : List BHist) :
    splitLefts (divisorFactorSplitsAux seen entries) =
      divisorFactorListsAux seen entries := by
  induction entries generalizing seen with
  | nil =>
      rfl
  | cons p ps ih =>
      unfold divisorFactorSplitsAux divisorFactorListsAux
      cases h : listContainsPrime p seen
      · change
          splitLefts
            (appendFactorSplitProducts
              (primePowerFactorSplits p (listPrimeCountNat p ps + 1))
              (divisorFactorSplitsAux (p :: seen) ps)) =
            appendFactorListProducts
              (primePowerFactorLists p (listPrimeCountNat p ps + 1))
              (divisorFactorListsAux (p :: seen) ps)
        rw [splitLefts_appendFactorSplitProducts]
        rw [splitLefts_primePowerFactorSplits]
        exact congrArg
          (fun tail =>
            appendFactorListProducts
              (primePowerFactorLists p (listPrimeCountNat p ps + 1)) tail)
          (ih (p :: seen))
      · exact ih seen

private theorem integerUpListSum_map_congr {α : Type}
    (xs : List α) (f g : α -> IntegerUp)
    (same : forall x : α, IntEq (f x) (g x)) :
    IntEq (integerUpListSum (xs.map f)) (integerUpListSum (xs.map g)) := by
  induction xs with
  | nil =>
      exact IntEq_refl intZero
  | cons x xs ih =>
      exact BEDC.Derived.IntUp.IntAdd_respects (same x) ih

theorem divisorFactorSplits_lefts (entries : List BHist) :
    splitLefts (divisorFactorSplits entries) = divisorFactorLists entries := by
  unfold divisorFactorSplits divisorFactorLists
  exact splitLefts_divisorFactorSplitsAux [] entries

private theorem integerUpListSum_mobius_one_over_splits
    (splits : List (List BHist × List BHist)) :
    IntEq
      (integerUpListSum
        (splits.map (fun split => IntMul (mobiusFunction split.1) (oneFunction split.2))))
      (mobiusFactorListSum (splitLefts splits)) := by
  induction splits with
  | nil =>
      exact IntEq_refl intZero
  | cons split splits ih =>
      have head :
          IntEq (IntMul (mobiusFunction split.1) (oneFunction split.2))
            (mobiusFactorsIntegerUp split.1) := by
        unfold mobiusFunction oneFunction
        exact BEDC.Derived.IntUp.IntMul_one (mobiusFactorsIntegerUp split.1)
      exact BEDC.Derived.IntUp.IntAdd_respects head ih

theorem mobiusDirichletUnit (entries : List BHist) :
    IntEq (dirichletConvolution mobiusFunction oneFunction entries)
      (epsilonFunction entries) := by
  unfold dirichletConvolution epsilonFunction
  have splitSum :
      IntEq
        (integerUpListSum
          ((divisorFactorSplits entries).map
            (fun split => IntMul (mobiusFunction split.1) (oneFunction split.2))))
        (mobiusFactorListSum (splitLefts (divisorFactorSplits entries))) :=
    integerUpListSum_mobius_one_over_splits (divisorFactorSplits entries)
  have projected :
      IntEq (mobiusFactorListSum (splitLefts (divisorFactorSplits entries)))
        (mobiusIndicatorIntegerUp entries) := by
    rw [divisorFactorSplits_lefts entries]
    exact sum_mobius_eq_indicator entries
  exact IntEq_trans splitSum projected

theorem dirichletConvolution_left_congr
    {f f' g : ArithmeticFunction} :
    ArithmeticFnEq f f' ->
      ArithmeticFnEq (dirichletConvolution f g) (dirichletConvolution f' g) := by
  intro same entries
  unfold dirichletConvolution
  generalize divisorFactorSplits entries = splits
  exact integerUpListSum_map_congr splits
    (fun split => IntMul (f split.1) (g split.2))
    (fun split => IntMul (f' split.1) (g split.2))
    (fun split =>
      BEDC.Derived.IntUp.IntMul_respects
        (same split.1) (IntEq_refl (g split.2)))

theorem dirichletConvolution_right_congr
    {f g g' : ArithmeticFunction} :
    ArithmeticFnEq g g' ->
      ArithmeticFnEq (dirichletConvolution f g) (dirichletConvolution f g') := by
  intro same entries
  unfold dirichletConvolution
  generalize divisorFactorSplits entries = splits
  exact integerUpListSum_map_congr splits
    (fun split => IntMul (f split.1) (g split.2))
    (fun split => IntMul (f split.1) (g' split.2))
    (fun split =>
      BEDC.Derived.IntUp.IntMul_respects
        (IntEq_refl (f split.1)) (same split.2))

theorem mobiusInversion
    (f g : ArithmeticFunction)
    (zetaRelation : ArithmeticFnEq g (dirichletConvolution f oneFunction))
    (convolutionAssoc :
      ArithmeticFnEq
        (dirichletConvolution mobiusFunction (dirichletConvolution f oneFunction))
        (dirichletConvolution (dirichletConvolution mobiusFunction oneFunction) f))
    (epsilonLeft : ArithmeticFnEq (dirichletConvolution epsilonFunction f) f) :
    ArithmeticFnEq (dirichletConvolution mobiusFunction g) f := by
  intro entries
  have substituteG :
      IntEq (dirichletConvolution mobiusFunction g entries)
        (dirichletConvolution mobiusFunction
          (dirichletConvolution f oneFunction) entries) :=
    dirichletConvolution_right_congr zetaRelation entries
  have reassociate :
      IntEq
        (dirichletConvolution mobiusFunction
          (dirichletConvolution f oneFunction) entries)
        (dirichletConvolution (dirichletConvolution mobiusFunction oneFunction)
          f entries) :=
    convolutionAssoc entries
  have replaceUnit :
      IntEq
        (dirichletConvolution (dirichletConvolution mobiusFunction oneFunction)
          f entries)
        (dirichletConvolution epsilonFunction f entries) :=
    dirichletConvolution_left_congr mobiusDirichletUnit entries
  exact IntEq_trans substituteG
    (IntEq_trans reassociate (IntEq_trans replaceUnit (epsilonLeft entries)))

end BEDC.Derived.MobiusInversionUp
