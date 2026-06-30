import BEDC.Derived.ArithmeticFnUp
import BEDC.Derived.DivisorFunctionUp
import BEDC.Derived.IntUp.CommRing
import BEDC.Derived.MobiusInversionUp

namespace BEDC.Derived.DirichletConvolutionUp

open BEDC.FKernel.Hist
open BEDC.Derived.ArithmeticFnUp
open BEDC.Derived.MobiusInversionUp
open BEDC.Derived.RationalUp

abbrev IntegerValue :=
  BEDC.Derived.PrimeUp.IntegerUp

abbrev ArithmeticFunction :=
  BEDC.Derived.MobiusInversionUp.ArithmeticFunction

def dirichletOne : ArithmeticFunction :=
  BEDC.Derived.MobiusInversionUp.oneFunction

def dirichletEpsilon : ArithmeticFunction :=
  BEDC.Derived.MobiusInversionUp.epsilonFunction

def dirichletMobius : ArithmeticFunction :=
  BEDC.Derived.MobiusInversionUp.mobiusFunction

def ArithmeticFnEq (f g : ArithmeticFunction) : Prop :=
  forall entries : List BHist, IntEq (f entries) (g entries)

def integerListFold {α : Type} (term : α -> IntegerValue) : List α -> IntegerValue
  | [] => intZero
  | x :: xs => IntAdd (term x) (integerListFold term xs)

def dirichletConvolution
    (f g : ArithmeticFunction) : ArithmeticFunction :=
  fun entries =>
    integerListFold
      (fun split => IntMul (f split.1) (g split.2))
      (divisorFactorSplits entries)

def leftInnerTripleExpansion
    (f g : ArithmeticFunction) (z : IntegerValue)
    (splits : List (List BHist × List BHist)) : IntegerValue :=
  integerListFold
    (fun split => IntMul (IntMul (f split.1) (g split.2)) z)
    splits

def rightInnerTripleExpansion
    (x : IntegerValue) (g h : ArithmeticFunction)
    (splits : List (List BHist × List BHist)) : IntegerValue :=
  integerListFold
    (fun split => IntMul (IntMul x (g split.1)) (h split.2))
    splits

def leftNestedTripleExpansion
    (f g h : ArithmeticFunction) (entries : List BHist) : IntegerValue :=
  integerListFold
    (fun outer =>
      leftInnerTripleExpansion f g (h outer.2)
        (divisorFactorSplits outer.1))
    (divisorFactorSplits entries)

def rightNestedTripleExpansion
    (f g h : ArithmeticFunction) (entries : List BHist) : IntegerValue :=
  integerListFold
    (fun outer =>
      rightInnerTripleExpansion (f outer.1) g h
        (divisorFactorSplits outer.2))
    (divisorFactorSplits entries)

theorem arithmeticFnEq_refl (f : ArithmeticFunction) :
    ArithmeticFnEq f f := by
  intro entries
  exact IntEq_refl (f entries)

theorem arithmeticFnEq_symm {f g : ArithmeticFunction} :
    ArithmeticFnEq f g -> ArithmeticFnEq g f := by
  intro same entries
  exact IntEq_symm (same entries)

theorem arithmeticFnEq_trans {f g h : ArithmeticFunction} :
    ArithmeticFnEq f g -> ArithmeticFnEq g h -> ArithmeticFnEq f h := by
  intro left right entries
  exact IntEq_trans (left entries) (right entries)

private theorem integerListFold_eq_integerUpListSum_map {α : Type}
    (term : α -> IntegerValue) :
    forall xs : List α,
      integerListFold term xs = integerUpListSum (xs.map term)
  | [] => rfl
  | x :: xs => by
      change
        IntAdd (term x) (integerListFold term xs) =
          IntAdd (term x) (integerUpListSum (xs.map term))
      exact congrArg (fun tail => IntAdd (term x) tail)
        (integerListFold_eq_integerUpListSum_map term xs)

private theorem integerListFold_congr {α : Type}
    (left right : α -> IntegerValue) :
    (forall x : α, IntEq (left x) (right x)) ->
      forall xs : List α,
        IntEq (integerListFold left xs) (integerListFold right xs)
  | _same, [] =>
      IntEq_refl intZero
  | same, x :: xs =>
      BEDC.Derived.IntUp.IntAdd_respects (same x)
        (integerListFold_congr left right same xs)

private theorem intMul_zero_left (x : IntegerValue) :
    IntEq (IntMul intZero x) intZero :=
  IntEq_trans
    (BEDC.Derived.IntUp.IntMul_comm intZero x)
    (BEDC.Derived.IntUp.IntMul_zero x)

private theorem intAdd_zero_left (x : IntegerValue) :
    IntEq (IntAdd intZero x) x :=
  IntEq_trans
    (BEDC.Derived.IntUp.IntAdd_comm intZero x)
    (BEDC.Derived.IntUp.IntAdd_zero x)

private theorem integerListFold_append {α : Type}
    (term : α -> IntegerValue) :
    forall xs ys : List α,
      IntEq (integerListFold term (xs ++ ys))
        (IntAdd (integerListFold term xs) (integerListFold term ys))
  | [], ys =>
      IntEq_symm (intAdd_zero_left (integerListFold term ys))
  | x :: xs, ys => by
      have tail :=
        integerListFold_append term xs ys
      have step :
          IntEq
            (IntAdd (term x) (integerListFold term (xs ++ ys)))
            (IntAdd (term x)
              (IntAdd (integerListFold term xs) (integerListFold term ys))) :=
        BEDC.Derived.IntUp.IntAdd_respects (IntEq_refl (term x)) tail
      exact IntEq_trans step
        (IntEq_symm
          (BEDC.Derived.IntUp.IntAdd_assoc
            (term x) (integerListFold term xs) (integerListFold term ys)))

theorem dirichletConvolution_matches_mobiusInversion
    (f g : ArithmeticFunction) :
    ArithmeticFnEq (dirichletConvolution f g)
      (BEDC.Derived.MobiusInversionUp.dirichletConvolution f g) := by
  intro entries
  unfold dirichletConvolution
  unfold BEDC.Derived.MobiusInversionUp.dirichletConvolution
  rw [integerListFold_eq_integerUpListSum_map]
  exact IntEq_refl _

theorem dirichletConvolution_left_congr
    {f f' g : ArithmeticFunction} :
    ArithmeticFnEq f f' ->
      ArithmeticFnEq (dirichletConvolution f g) (dirichletConvolution f' g) := by
  intro same entries
  unfold dirichletConvolution
  exact integerListFold_congr
    (fun split => IntMul (f split.1) (g split.2))
    (fun split => IntMul (f' split.1) (g split.2))
    (fun split =>
      BEDC.Derived.IntUp.IntMul_respects
        (same split.1) (IntEq_refl (g split.2)))
    (divisorFactorSplits entries)

theorem dirichletConvolution_right_congr
    {f g g' : ArithmeticFunction} :
    ArithmeticFnEq g g' ->
      ArithmeticFnEq (dirichletConvolution f g) (dirichletConvolution f g') := by
  intro same entries
  unfold dirichletConvolution
  exact integerListFold_congr
    (fun split => IntMul (f split.1) (g split.2))
    (fun split => IntMul (f split.1) (g' split.2))
    (fun split =>
      BEDC.Derived.IntUp.IntMul_respects
        (IntEq_refl (f split.1)) (same split.2))
    (divisorFactorSplits entries)

private theorem leftInnerTripleExpansion_sound_from_splits
    (f g : ArithmeticFunction) (z : IntegerValue) :
    forall splits : List (List BHist × List BHist),
      IntEq
        (IntMul
          (integerListFold
            (fun split => IntMul (f split.1) (g split.2)) splits)
          z)
        (leftInnerTripleExpansion f g z splits)
  | [] =>
      intMul_zero_left z
  | split :: rest => by
      let x : IntegerValue := IntMul (f split.1) (g split.2)
      let y : IntegerValue :=
        integerListFold
          (fun split => IntMul (f split.1) (g split.2)) rest
      change
        IntEq (IntMul (IntAdd x y) z)
          (IntAdd (IntMul x z)
            (leftInnerTripleExpansion f g z rest))
      have distrib :
          IntEq (IntMul (IntAdd x y) z)
            (IntAdd (IntMul x z) (IntMul y z)) :=
        BEDC.Derived.IntUp.IntMul_add_distrib_right x y z
      have tail :
          IntEq (IntMul y z)
            (leftInnerTripleExpansion f g z rest) := by
        exact leftInnerTripleExpansion_sound_from_splits f g z rest
      exact IntEq_trans distrib
        (BEDC.Derived.IntUp.IntAdd_respects (IntEq_refl (IntMul x z)) tail)

private theorem rightInnerTripleExpansion_sound_from_splits
    (x : IntegerValue) (g h : ArithmeticFunction) :
    forall splits : List (List BHist × List BHist),
      IntEq
        (IntMul x
          (integerListFold
            (fun split => IntMul (g split.1) (h split.2)) splits))
        (rightInnerTripleExpansion x g h splits)
  | [] =>
      BEDC.Derived.IntUp.IntMul_zero x
  | split :: rest => by
      let y : IntegerValue := IntMul (g split.1) (h split.2)
      let z : IntegerValue :=
        integerListFold
          (fun split => IntMul (g split.1) (h split.2)) rest
      change
        IntEq (IntMul x (IntAdd y z))
          (IntAdd (IntMul (IntMul x (g split.1)) (h split.2))
            (rightInnerTripleExpansion x g h rest))
      have distrib :
          IntEq (IntMul x (IntAdd y z))
            (IntAdd (IntMul x y) (IntMul x z)) :=
        BEDC.Derived.IntUp.IntMul_add_distrib x y z
      have head :
          IntEq (IntMul x y)
            (IntMul (IntMul x (g split.1)) (h split.2)) :=
        IntEq_symm
          (BEDC.Derived.IntUp.IntMul_assoc x (g split.1) (h split.2))
      have tail :
          IntEq (IntMul x z)
            (rightInnerTripleExpansion x g h rest) := by
        exact rightInnerTripleExpansion_sound_from_splits x g h rest
      exact IntEq_trans distrib
        (BEDC.Derived.IntUp.IntAdd_respects head tail)

private theorem leftInnerTripleExpansion_sound
    (f g : ArithmeticFunction) (z : IntegerValue) (entries : List BHist) :
    IntEq (IntMul (dirichletConvolution f g entries) z)
      (leftInnerTripleExpansion f g z (divisorFactorSplits entries)) := by
  unfold dirichletConvolution
  exact leftInnerTripleExpansion_sound_from_splits f g z
    (divisorFactorSplits entries)

private theorem rightInnerTripleExpansion_sound
    (x : IntegerValue) (g h : ArithmeticFunction) (entries : List BHist) :
    IntEq (IntMul x (dirichletConvolution g h entries))
      (rightInnerTripleExpansion x g h (divisorFactorSplits entries)) := by
  unfold dirichletConvolution
  exact rightInnerTripleExpansion_sound_from_splits x g h
    (divisorFactorSplits entries)

theorem left_nested_convolution_expands_to_triples
    (f g h : ArithmeticFunction) (entries : List BHist) :
    IntEq
      (dirichletConvolution (dirichletConvolution f g) h entries)
      (leftNestedTripleExpansion f g h entries) := by
  unfold dirichletConvolution
  unfold leftNestedTripleExpansion
  induction divisorFactorSplits entries with
  | nil =>
      exact IntEq_refl intZero
  | cons outer rest ih =>
      exact BEDC.Derived.IntUp.IntAdd_respects
        (leftInnerTripleExpansion_sound f g (h outer.2) outer.1)
        ih

theorem right_nested_convolution_expands_to_triples
    (f g h : ArithmeticFunction) (entries : List BHist) :
    IntEq
      (dirichletConvolution f (dirichletConvolution g h) entries)
      (rightNestedTripleExpansion f g h entries) := by
  unfold dirichletConvolution
  unfold rightNestedTripleExpansion
  induction divisorFactorSplits entries with
  | nil =>
      exact IntEq_refl intZero
  | cons outer rest ih =>
      exact BEDC.Derived.IntUp.IntAdd_respects
        (rightInnerTripleExpansion_sound (f outer.1) g h outer.2)
        ih

def MatchingTripleExpansion
    (f g h : ArithmeticFunction) : Prop :=
  forall entries : List BHist,
    IntEq (leftNestedTripleExpansion f g h entries)
      (rightNestedTripleExpansion f g h entries)

theorem dirichletConvolution_assoc_from_matching_triples
    (f g h : ArithmeticFunction) :
    MatchingTripleExpansion f g h ->
      ArithmeticFnEq
        (dirichletConvolution (dirichletConvolution f g) h)
        (dirichletConvolution f (dirichletConvolution g h)) := by
  intro matching entries
  exact IntEq_trans
    (left_nested_convolution_expands_to_triples f g h entries)
    (IntEq_trans (matching entries)
      (IntEq_symm
        (right_nested_convolution_expands_to_triples f g h entries)))

theorem mobius_mul_one_eq_epsilon :
    ArithmeticFnEq
      (dirichletConvolution dirichletMobius dirichletOne)
      dirichletEpsilon := by
  intro entries
  exact IntEq_trans
    (dirichletConvolution_matches_mobiusInversion
      dirichletMobius dirichletOne entries)
    (BEDC.Derived.MobiusInversionUp.mobiusDirichletUnit entries)

theorem mobiusInversion
    (f g : ArithmeticFunction)
    (zetaRelation :
      ArithmeticFnEq g (dirichletConvolution f dirichletOne))
    (convolutionAssoc :
      ArithmeticFnEq
        (dirichletConvolution dirichletMobius
          (dirichletConvolution f dirichletOne))
        (dirichletConvolution
          (dirichletConvolution dirichletMobius dirichletOne) f))
    (epsilonLeft :
      ArithmeticFnEq (dirichletConvolution dirichletEpsilon f) f) :
    ArithmeticFnEq (dirichletConvolution dirichletMobius g) f := by
  have zetaOld :
      BEDC.Derived.MobiusInversionUp.ArithmeticFnEq g
        (BEDC.Derived.MobiusInversionUp.dirichletConvolution
          f dirichletOne) := by
    intro entries
    exact IntEq_trans (zetaRelation entries)
      (dirichletConvolution_matches_mobiusInversion
        f dirichletOne entries)
  have assocOld :
      BEDC.Derived.MobiusInversionUp.ArithmeticFnEq
        (BEDC.Derived.MobiusInversionUp.dirichletConvolution
          dirichletMobius
          (BEDC.Derived.MobiusInversionUp.dirichletConvolution
            f dirichletOne))
        (BEDC.Derived.MobiusInversionUp.dirichletConvolution
          (BEDC.Derived.MobiusInversionUp.dirichletConvolution
            dirichletMobius dirichletOne) f) := by
    intro entries
    have leftToNew :
        IntEq
          (BEDC.Derived.MobiusInversionUp.dirichletConvolution
            dirichletMobius
            (BEDC.Derived.MobiusInversionUp.dirichletConvolution
              f dirichletOne) entries)
          (dirichletConvolution dirichletMobius
            (dirichletConvolution f dirichletOne) entries) := by
      exact IntEq_trans
        (IntEq_symm
          (dirichletConvolution_matches_mobiusInversion
            dirichletMobius
            (BEDC.Derived.MobiusInversionUp.dirichletConvolution
              f dirichletOne) entries))
        (dirichletConvolution_right_congr
          (fun e =>
            IntEq_symm
              (dirichletConvolution_matches_mobiusInversion
                f dirichletOne e)) entries)
    have rightFromNew :
        IntEq
          (dirichletConvolution
            (dirichletConvolution dirichletMobius dirichletOne) f entries)
          (BEDC.Derived.MobiusInversionUp.dirichletConvolution
            (BEDC.Derived.MobiusInversionUp.dirichletConvolution
              dirichletMobius dirichletOne) f entries) := by
      exact IntEq_trans
        (dirichletConvolution_left_congr
          (fun e =>
            dirichletConvolution_matches_mobiusInversion
              dirichletMobius dirichletOne e) entries)
        (dirichletConvolution_matches_mobiusInversion
          (BEDC.Derived.MobiusInversionUp.dirichletConvolution
            dirichletMobius dirichletOne) f entries)
    exact IntEq_trans leftToNew
      (IntEq_trans (convolutionAssoc entries) rightFromNew)
  have epsilonOld :
      BEDC.Derived.MobiusInversionUp.ArithmeticFnEq
        (BEDC.Derived.MobiusInversionUp.dirichletConvolution
          dirichletEpsilon f) f := by
    intro entries
    exact IntEq_trans
      (IntEq_symm
        (dirichletConvolution_matches_mobiusInversion
          dirichletEpsilon f entries))
      (epsilonLeft entries)
  intro entries
  exact IntEq_trans
    (dirichletConvolution_matches_mobiusInversion
      dirichletMobius g entries)
    (BEDC.Derived.MobiusInversionUp.mobiusInversion f g
      zetaOld assocOld epsilonOld entries)

end BEDC.Derived.DirichletConvolutionUp
