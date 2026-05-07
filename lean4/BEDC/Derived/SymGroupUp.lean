import BEDC.Derived.GroupUp
import BEDC.Derived.PermutationUp

namespace BEDC.Derived.SymGroupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.Derived.GroupUp
open BEDC.Derived.PermutationUp

theorem SymGroupCarrier_obligation [AskSetup] [PackageSetup]
    {src tgt graph invGraph comp action ledger : BHist}
    {srcBundle tgtBundle : ProbeBundle ProbeName} {srcPkg tgtPkg : Pkg} :
    PermutationBijectionSourceRow src tgt graph invGraph comp action ledger srcBundle tgtBundle
        srcPkg tgtPkg ->
      hsame src BHist.Empty ->
        hsame tgt BHist.Empty ->
          GroupSingletonCarrier graph ∧ GroupSingletonCarrier invGraph ∧
            GroupSingletonCarrier comp ∧ GroupSingletonCarrier action ∧
              GroupSingletonCarrier ledger := by
  intro row srcEmpty tgtEmpty
  cases srcEmpty
  cases tgtEmpty
  have graphCarrier : GroupSingletonCarrier graph :=
    row.right.right.left
  have invGraphCarrier : GroupSingletonCarrier invGraph :=
    row.right.right.right.left
  have compCarrier : GroupSingletonCarrier comp := by
    cases graphCarrier
    cases invGraphCarrier
    exact row.right.right.right.right.left
  have actionCarrier : GroupSingletonCarrier action := by
    cases graphCarrier
    exact row.right.right.right.right.right.left
  have ledgerCarrier : GroupSingletonCarrier ledger := by
    cases compCarrier
    cases actionCarrier
    exact row.right.right.right.right.right.right.left
  exact ⟨graphCarrier, invGraphCarrier, compCarrier, actionCarrier, ledgerCarrier⟩

end BEDC.Derived.SymGroupUp
