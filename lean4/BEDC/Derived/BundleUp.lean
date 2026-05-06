import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.BundleUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def BundleLocalTrivPkg
    (base total projection fibre ledger : BHist) (trivializations transitions : ProbeBundle BHist) :
    Prop :=
  UnaryHistory base ∧ UnaryHistory total ∧ UnaryHistory projection ∧ UnaryHistory fibre ∧
    UnaryHistory ledger ∧ Cont base total projection ∧ Cont projection fibre ledger ∧
      (∀ {row : BHist}, InBundle row trivializations -> UnaryHistory row) ∧
        (∀ {row : BHist}, InBundle row transitions -> UnaryHistory row)

theorem BundleLocalTrivPkg_transition_cocycle_ledger_closure
    {base total projection fibre ledger tij tjk tik composed displayed : BHist}
    {trivializations transitions : ProbeBundle BHist} :
    BundleLocalTrivPkg base total projection fibre ledger trivializations transitions ->
      InBundle tij transitions ->
      InBundle tjk transitions ->
      InBundle tik transitions ->
      Cont tij tjk composed ->
      Cont tik ledger displayed ->
        hsame displayed (append tik ledger) ∧ UnaryHistory composed ∧ UnaryHistory displayed := by
  intro package tijInTransitions tjkInTransitions tikInTransitions composedReadback displayedReadback
  have ledgerUnary : UnaryHistory ledger :=
    package.right.right.right.right.left
  have transitionRowsUnary :
      ∀ {row : BHist}, InBundle row transitions -> UnaryHistory row :=
    package.right.right.right.right.right.right.right.right
  have tijUnary : UnaryHistory tij :=
    transitionRowsUnary tijInTransitions
  have tjkUnary : UnaryHistory tjk :=
    transitionRowsUnary tjkInTransitions
  have tikUnary : UnaryHistory tik :=
    transitionRowsUnary tikInTransitions
  have composedUnary : UnaryHistory composed :=
    unary_cont_closed tijUnary tjkUnary composedReadback
  have displayedUnary : UnaryHistory displayed :=
    unary_cont_closed tikUnary ledgerUnary displayedReadback
  exact And.intro displayedReadback (And.intro composedUnary displayedUnary)

end BEDC.Derived.BundleUp
