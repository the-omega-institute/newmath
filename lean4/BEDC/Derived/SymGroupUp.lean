import BEDC.Derived.GroupUp
import BEDC.Derived.PermutationUp

namespace BEDC.Derived.SymGroupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.PermutationUp

def SymGroupPermutationCarrier [AskSetup] [PackageSetup]
    (src tgt graph invGraph comp action ledger : BHist)
    (srcBundle tgtBundle : ProbeBundle ProbeName) (srcPkg tgtPkg : Pkg) : Prop :=
  PermutationBijectionSourceRow src tgt graph invGraph comp action ledger srcBundle tgtBundle
      srcPkg tgtPkg ∧
    GroupSingletonCarrier comp ∧ GroupSingletonCarrier action

theorem SymGroupPermutationCarrier_carrier_obligation [AskSetup] [PackageSetup]
    {src tgt graph invGraph comp action ledger : BHist}
    {srcBundle tgtBundle : ProbeBundle ProbeName} {srcPkg tgtPkg : Pkg} :
    SymGroupPermutationCarrier src tgt graph invGraph comp action ledger srcBundle tgtBundle
        srcPkg tgtPkg ->
      PermutationBijectionSourceRow src tgt graph invGraph comp action ledger srcBundle
          tgtBundle srcPkg tgtPkg ∧
        UnaryHistory graph ∧ UnaryHistory invGraph ∧ UnaryHistory action ∧
          GroupSingletonCarrier comp ∧ GroupSingletonCarrier action ∧
            PkgSig srcBundle src srcPkg ∧ PkgSig tgtBundle tgt tgtPkg := by
  intro carrier
  have row :
      PermutationBijectionSourceRow src tgt graph invGraph comp action ledger srcBundle
        tgtBundle srcPkg tgtPkg := carrier.left
  have surface := PermutationBijectionSourceRow_carrier_surface row
  exact And.intro row
    (And.intro surface.left
      (And.intro surface.right.left
        (And.intro surface.right.right.left
          (And.intro carrier.right.left
            (And.intro carrier.right.right
              surface.right.right.right.right.right.right.right.right.right)))))

end BEDC.Derived.SymGroupUp
