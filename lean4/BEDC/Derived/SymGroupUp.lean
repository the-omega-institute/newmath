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

def SymGroupPermutationCarrier [AskSetup] [PackageSetup]
    (src tgt graph invGraph comp action ledger : BHist)
    (srcBundle tgtBundle : ProbeBundle ProbeName) (srcPkg tgtPkg : Pkg) : Prop :=
  PermutationBijectionSourceRow src tgt graph invGraph comp action ledger srcBundle tgtBundle
      srcPkg tgtPkg ∧
    GroupSingletonCarrier comp

theorem SymGroupPermutationCarrier_carrier_obligation [AskSetup] [PackageSetup]
    {src tgt graph invGraph comp action ledger : BHist}
    {srcBundle tgtBundle : ProbeBundle ProbeName} {srcPkg tgtPkg : Pkg} :
    SymGroupPermutationCarrier src tgt graph invGraph comp action ledger srcBundle tgtBundle
        srcPkg tgtPkg ->
      PermutationBijectionSourceRow src tgt graph invGraph comp action ledger srcBundle
          tgtBundle srcPkg tgtPkg ∧
        GroupSingletonCarrier comp ∧ UnaryHistory graph ∧ UnaryHistory invGraph ∧
          UnaryHistory action ∧ UnaryHistory ledger ∧
            Cont graph invGraph comp ∧ Cont src graph action ∧ Cont comp action ledger ∧
              PkgSig srcBundle src srcPkg ∧ PkgSig tgtBundle tgt tgtPkg := by
  intro carrier
  have surface := PermutationBijectionSourceRow_carrier_surface carrier.left
  exact And.intro carrier.left
    (And.intro carrier.right
      (And.intro surface.left
        (And.intro surface.right.left
          (And.intro surface.right.right.left
            (And.intro surface.right.right.right.left
                (And.intro surface.right.right.right.right.right.right.left
                  (And.intro surface.right.right.right.right.right.right.right.left
                    (And.intro surface.right.right.right.right.right.right.right.right.left
                      surface.right.right.right.right.right.right.right.right.right))))))))

end BEDC.Derived.SymGroupUp
