import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.BundleUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def BundleLocalTrivPkg
    (base total projection fibre transition ledger : BHist) (trivs : ProbeBundle BHist) :
    Prop :=
  UnaryHistory base ∧ UnaryHistory total ∧ UnaryHistory projection ∧ UnaryHistory fibre ∧
    UnaryHistory transition ∧ UnaryHistory ledger ∧ Cont base projection total ∧
      Cont total fibre transition ∧ InBundle transition trivs

theorem BundleLocalTrivPkg_transition_stability
    {base total projection fibre transition ledger base' total' projection' fibre' transition'
      ledger' : BHist}
    {trivs : ProbeBundle BHist} :
    BundleLocalTrivPkg base total projection fibre transition ledger trivs ->
      hsame base base' -> hsame total total' -> hsame projection projection' ->
        hsame fibre fibre' -> hsame transition transition' -> hsame ledger ledger' ->
          BundleLocalTrivPkg base' total' projection' fibre' transition' ledger' trivs ∧
            hsame transition transition' ∧ UnaryHistory transition' ∧
              InBundle transition' trivs := by
  intro pkg sameBase sameTotal sameProjection sameFibre sameTransition sameLedger
  cases sameBase
  cases sameTotal
  cases sameProjection
  cases sameFibre
  cases sameTransition
  cases sameLedger
  exact And.intro pkg
    (And.intro (hsame_refl transition)
      (And.intro pkg.right.right.right.right.left
        pkg.right.right.right.right.right.right.right.right))

end BEDC.Derived.BundleUp
