import BEDC.Derived.GroupUp
import BEDC.Derived.PermutationUp

namespace BEDC.Derived.SymGroupUp

open BEDC.Derived.GroupUp
open BEDC.Derived.PermutationUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SymGroupPermutationCarrier_obligation [AskSetup] [PackageSetup]
    {src tgt graph invGraph comp action ledger : BHist}
    {srcBundle tgtBundle : ProbeBundle ProbeName} {srcPkg tgtPkg : Pkg} :
    PermutationBijectionSourceRow src tgt graph invGraph comp action ledger srcBundle tgtBundle
        srcPkg tgtPkg ->
      GroupSingletonCarrier BHist.Empty ∧ UnaryHistory graph ∧ UnaryHistory invGraph ∧
        UnaryHistory action ∧ UnaryHistory ledger ∧ hsame comp (append graph invGraph) ∧
          hsame action (append src graph) := by
  intro row
  have carrierRows :
      UnaryHistory graph ∧ UnaryHistory invGraph ∧ UnaryHistory action ∧
        UnaryHistory ledger ∧ Cont src tgt graph ∧ Cont tgt src invGraph ∧
          Cont graph invGraph comp ∧ Cont src graph action ∧ Cont comp action ledger ∧
            PkgSig srcBundle src srcPkg ∧ PkgSig tgtBundle tgt tgtPkg :=
    PermutationBijectionSourceRow_carrier_surface row
  have scopeRows :
      hsame comp (append graph invGraph) ∧ hsame action (append src graph) ∧
        hsame ledger (append (append graph invGraph) (append src graph)) :=
    PermutationBijectionSourceRow_composition_action_ledger_scope row
  exact And.intro (hsame_refl BHist.Empty)
    (And.intro carrierRows.left
      (And.intro carrierRows.right.left
        (And.intro carrierRows.right.right.left
          (And.intro carrierRows.right.right.right.left
            (And.intro scopeRows.left scopeRows.right.left)))))

end BEDC.Derived.SymGroupUp
