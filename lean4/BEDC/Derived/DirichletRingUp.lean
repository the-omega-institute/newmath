import BEDC.Derived.ArithmeticFnUp
import BEDC.Derived.DivisorFunctionUp
import BEDC.Derived.IntUp.CommRing
import BEDC.Derived.MobiusInversionUp

namespace BEDC.Derived.DirichletRingUp

open BEDC.FKernel.Hist
open BEDC.Derived.ArithmeticFnUp
open BEDC.Derived.IntUp
open BEDC.Derived.MobiusInversionUp
open BEDC.Derived.RationalUp

abbrev ArithmeticFunction :=
  BEDC.Derived.MobiusInversionUp.ArithmeticFunction

def dirichletOne : ArithmeticFunction :=
  BEDC.Derived.MobiusInversionUp.oneFunction

def dirichletEpsilon : ArithmeticFunction :=
  BEDC.Derived.MobiusInversionUp.epsilonFunction

def dirichletMobius : ArithmeticFunction :=
  BEDC.Derived.MobiusInversionUp.mobiusFunction

def dirichletConvolution
    (f g : ArithmeticFunction) : ArithmeticFunction :=
  BEDC.Derived.MobiusInversionUp.dirichletConvolution f g

def ArithmeticFnEq (f g : ArithmeticFunction) : Prop :=
  BEDC.Derived.MobiusInversionUp.ArithmeticFnEq f g

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

theorem dirichletConvolution_left_congr
    {f f' g : ArithmeticFunction} :
    ArithmeticFnEq f f' ->
      ArithmeticFnEq (dirichletConvolution f g) (dirichletConvolution f' g) := by
  intro same
  exact BEDC.Derived.MobiusInversionUp.dirichletConvolution_left_congr same

theorem dirichletConvolution_right_congr
    {f g g' : ArithmeticFunction} :
    ArithmeticFnEq g g' ->
      ArithmeticFnEq (dirichletConvolution f g) (dirichletConvolution f g') := by
  intro same
  exact BEDC.Derived.MobiusInversionUp.dirichletConvolution_right_congr same

theorem mobius_mul_one_eq_epsilon :
    ArithmeticFnEq
      (dirichletConvolution dirichletMobius dirichletOne)
      dirichletEpsilon := by
  intro entries
  exact BEDC.Derived.MobiusInversionUp.mobiusDirichletUnit entries

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
    ArithmeticFnEq (dirichletConvolution dirichletMobius g) f :=
  BEDC.Derived.MobiusInversionUp.mobiusInversion f g
    zetaRelation convolutionAssoc epsilonLeft

end BEDC.Derived.DirichletRingUp
