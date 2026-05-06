import BEDC.Derived.ManifoldUp

namespace BEDC.Derived.ManifoldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem ManifoldScopedBoundaryPackage_field_coverage {carrier i j k pair triple : BHist} :
    ManifoldScopedBoundaryPackage carrier i j k pair triple ->
      UnaryHistory carrier ∧ UnaryHistory i ∧ UnaryHistory j ∧ UnaryHistory k ∧
        Cont i j pair ∧ Cont pair k triple ∧ UnaryHistory pair ∧ UnaryHistory triple ∧
          hsame pair (append i j) ∧ hsame triple (append pair k) := by
  intro package
  have carrierUnary : UnaryHistory carrier := package.left
  have iUnary : UnaryHistory i := package.right.left
  have jUnary : UnaryHistory j := package.right.right.left
  have kUnary : UnaryHistory k := package.right.right.right.left
  have pairRow : Cont i j pair := package.right.right.right.right.left
  have tripleRow : Cont pair k triple := package.right.right.right.right.right
  have closure := ManifoldScopedBoundaryPackage_pair_transition_closure package
  have pairUnary : UnaryHistory pair := closure.left
  have pairSame : hsame pair (append i j) := closure.right.left
  have tripleUnary : UnaryHistory triple := closure.right.right.left
  have tripleSame : hsame triple (append pair k) := closure.right.right.right
  exact And.intro carrierUnary
    (And.intro iUnary
      (And.intro jUnary
        (And.intro kUnary
          (And.intro pairRow
            (And.intro tripleRow
              (And.intro pairUnary
                (And.intro tripleUnary (And.intro pairSame tripleSame))))))))

end BEDC.Derived.ManifoldUp
