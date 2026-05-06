import BEDC.Derived.ComplexLimitUp

namespace BEDC.Derived.ComplexLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ComplexRegularSequence_accepted_pair_unary_witness
    {s N : BHist -> BHist} {k n m : BHist} :
    ComplexRegularSequence s N -> UnaryHistory k -> UnaryHistory n -> UnaryHistory m ->
      Cont (N k) n n -> Cont (N k) m m ->
        exists d : BHist, ComplexDistance (s n) (s m) d ∧
          UnaryHistory (s n) ∧ UnaryHistory (s m) ∧ UnaryHistory d := by
  intro regular unaryK unaryN unaryM controlledN controlledM
  cases regular k n m unaryK unaryN unaryM controlledN controlledM with
  | intro d distance =>
      exact Exists.intro d
        (And.intro distance
          (And.intro distance.left
            (And.intro distance.right.left distance.right.right.left)))

end BEDC.Derived.ComplexLimitUp
