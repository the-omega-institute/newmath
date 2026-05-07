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

theorem SymGroupPermutationCarrier_group_surface [AskSetup] [PackageSetup]
    {src tgt graph invGraph comp action ledger : BHist}
    {srcBundle tgtBundle : ProbeBundle ProbeName} {srcPkg tgtPkg : Pkg} :
    PermutationBijectionSourceRow src tgt graph invGraph comp action ledger srcBundle tgtBundle
        srcPkg tgtPkg ->
      GroupSingletonCarrier BHist.Empty ∧ UnaryHistory graph ∧ UnaryHistory invGraph ∧
        UnaryHistory action ∧ UnaryHistory ledger ∧ Cont graph invGraph comp ∧
          Cont src graph action ∧ Cont comp action ledger ∧
            PkgSig srcBundle src srcPkg ∧ PkgSig tgtBundle tgt tgtPkg := by
  intro row
  have surface := PermutationBijectionSourceRow_carrier_surface row
  exact And.intro (hsame_refl BHist.Empty)
    (And.intro surface.left
      (And.intro surface.right.left
        (And.intro surface.right.right.left
          (And.intro surface.right.right.right.left
            (And.intro surface.right.right.right.right.right.right.left
              (And.intro surface.right.right.right.right.right.right.right.left
                (And.intro surface.right.right.right.right.right.right.right.right.left
                  surface.right.right.right.right.right.right.right.right.right)))))))

end BEDC.Derived.SymGroupUp
