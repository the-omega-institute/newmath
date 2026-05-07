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

theorem SymGroupPermutationCarrier_composition_inverse_action_obligations [AskSetup] [PackageSetup]
    {src tgt graph invGraph comp action ledger : BHist}
    {srcBundle tgtBundle : ProbeBundle ProbeName} {srcPkg tgtPkg : Pkg} :
    SymGroupPermutationCarrier src tgt graph invGraph comp action ledger srcBundle tgtBundle
        srcPkg tgtPkg ->
      GroupSingletonCarrier comp ∧
        GroupSingletonCarrier (GroupSingletonInv comp) ∧
          GroupSingletonClassifier (GroupSingletonMul GroupSingletonUnit comp) comp ∧
            GroupSingletonClassifier (GroupSingletonMul comp GroupSingletonUnit) comp ∧
              GroupSingletonClassifier
                (GroupSingletonMul (GroupSingletonInv comp) comp) GroupSingletonUnit ∧
                GroupSingletonClassifier
                  (GroupSingletonMul comp (GroupSingletonInv comp)) GroupSingletonUnit ∧
                  Cont graph invGraph comp ∧ Cont src graph action ∧ Cont comp action ledger := by
  intro carrier
  have obligation := SymGroupPermutationCarrier_carrier_obligation carrier
  have laws := GroupSingletonHistory_laws
  have compCarrier : GroupSingletonCarrier comp := obligation.right.left
  have invCarrier : GroupSingletonCarrier (GroupSingletonInv comp) :=
    laws.right.right.left compCarrier
  have leftUnit : GroupSingletonClassifier (GroupSingletonMul GroupSingletonUnit comp) comp :=
    laws.right.right.right.left compCarrier
  have rightUnit : GroupSingletonClassifier (GroupSingletonMul comp GroupSingletonUnit) comp :=
    laws.right.right.right.right.left compCarrier
  have leftInv :
      GroupSingletonClassifier (GroupSingletonMul (GroupSingletonInv comp) comp)
        GroupSingletonUnit :=
    laws.right.right.right.right.right.left compCarrier
  have rightInv :
      GroupSingletonClassifier (GroupSingletonMul comp (GroupSingletonInv comp))
        GroupSingletonUnit :=
    laws.right.right.right.right.right.right compCarrier
  exact And.intro compCarrier
    (And.intro invCarrier
      (And.intro leftUnit
        (And.intro rightUnit
          (And.intro leftInv
            (And.intro rightInv
              (And.intro obligation.right.right.right.right.right.right.left
                (And.intro obligation.right.right.right.right.right.right.right.left
                  obligation.right.right.right.right.right.right.right.right.left)))))))

end BEDC.Derived.SymGroupUp
