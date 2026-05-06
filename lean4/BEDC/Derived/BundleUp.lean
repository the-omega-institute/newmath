import BEDC.FKernel.Bundle
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.BundleUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def BundleRowsUnary : ProbeBundle BHist -> Prop
  | .Bnil => True
  | .Bcons row tail => UnaryHistory row ∧ BundleRowsUnary tail

def BundleLocalTrivPackage
    (base total projection fiber : BHist) (trivs transitions : ProbeBundle BHist)
    (ledger : BHist) : Prop :=
  UnaryHistory base ∧ UnaryHistory total ∧ UnaryHistory projection ∧ UnaryHistory fiber ∧
    UnaryHistory ledger ∧ BundleRowsUnary trivs ∧ BundleRowsUnary transitions

theorem BundleLocalTrivPackage_carrier_projection
    {base total projection fiber ledger : BHist} {trivs transitions : ProbeBundle BHist} :
    BundleLocalTrivPackage base total projection fiber trivs transitions ledger ->
      UnaryHistory base ∧ UnaryHistory total ∧ UnaryHistory projection ∧ UnaryHistory fiber ∧
        UnaryHistory ledger ∧ BundleRowsUnary trivs ∧ BundleRowsUnary transitions := by
  intro package
  exact And.intro package.left
    (And.intro package.right.left
      (And.intro package.right.right.left
        (And.intro package.right.right.right.left
          (And.intro package.right.right.right.right.left
            (And.intro package.right.right.right.right.right.left
              package.right.right.right.right.right.right)))))

end BEDC.Derived.BundleUp
