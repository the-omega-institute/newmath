import BEDC.Derived.ComplexLimitUp

namespace BEDC.Derived.ComplexLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ComplexRegularSequence_cauchy_witness_package {s N : BHist -> BHist} :
    ComplexRegularSequence s N ->
      forall k n m : BHist, UnaryHistory k -> UnaryHistory n -> UnaryHistory m ->
        Cont (N k) n n -> Cont (N k) m m ->
          exists d : BHist, ComplexDistance (s n) (s m) d ∧ UnaryHistory d := by
  intro regular k n m unaryK unaryN unaryM controlledN controlledM
  cases regular k n m unaryK unaryN unaryM controlledN controlledM with
  | intro d distance =>
      exact Exists.intro d (And.intro distance distance.right.right.left)

end BEDC.Derived.ComplexLimitUp
