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

theorem SymGroupPermutationClassifier_stability [AskSetup] [PackageSetup]
    {src tgt graph invGraph comp action ledger src' tgt' graph' invGraph' comp' action'
      ledger' : BHist}
    {srcBundle tgtBundle : ProbeBundle ProbeName} {srcPkg tgtPkg : Pkg} :
    SymGroupPermutationCarrier src tgt graph invGraph comp action ledger srcBundle tgtBundle
        srcPkg tgtPkg ->
      hsame src src' -> hsame tgt tgt' -> PkgSig srcBundle src' srcPkg ->
        PkgSig tgtBundle tgt' tgtPkg -> Cont src' tgt' graph' ->
          Cont tgt' src' invGraph' -> Cont graph' invGraph' comp' ->
            Cont src' graph' action' -> Cont comp' action' ledger' ->
              SymGroupPermutationCarrier src' tgt' graph' invGraph' comp' action' ledger'
                  srcBundle tgtBundle srcPkg tgtPkg ∧
                hsame graph graph' ∧ hsame invGraph invGraph' ∧ hsame comp comp' ∧
                  hsame action action' ∧ hsame ledger ledger' := by
  intro carrier sameSrc sameTgt srcPkg' tgtPkg' graphCont' invGraphCont' compCont'
    actionCont' ledgerCont'
  have transported :=
    PermutationBijectionSourceRow_endpoint_package_hsame_transport carrier.left sameSrc sameTgt
      srcPkg' tgtPkg' graphCont' invGraphCont' compCont' actionCont' ledgerCont'
  have groupCarrier' : GroupSingletonCarrier comp' :=
    hsame_trans (hsame_symm transported.right.right.right.left) carrier.right
  exact And.intro
    (And.intro transported.left groupCarrier')
    transported.right

end BEDC.Derived.SymGroupUp
