import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PermutationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PermutationBijectionSourceRow [AskSetup] [PackageSetup]
    (src tgt graph invGraph comp action ledger : BHist)
    (srcBundle tgtBundle : ProbeBundle ProbeName) (srcPkg tgtPkg : Pkg) : Prop :=
  UnaryHistory src ∧ UnaryHistory tgt ∧ Cont src tgt graph ∧ Cont tgt src invGraph ∧
    Cont graph invGraph comp ∧ Cont src graph action ∧ Cont comp action ledger ∧
      PkgSig srcBundle src srcPkg ∧ PkgSig tgtBundle tgt tgtPkg

theorem PermutationBijectionSourceRow_carrier_surface [AskSetup] [PackageSetup]
    {src tgt graph invGraph comp action ledger : BHist}
    {srcBundle tgtBundle : ProbeBundle ProbeName} {srcPkg tgtPkg : Pkg} :
    PermutationBijectionSourceRow src tgt graph invGraph comp action ledger srcBundle
        tgtBundle srcPkg tgtPkg ->
      UnaryHistory graph ∧ UnaryHistory invGraph ∧ UnaryHistory action ∧
        UnaryHistory ledger ∧ Cont src tgt graph ∧ Cont tgt src invGraph ∧
          Cont graph invGraph comp ∧ Cont src graph action ∧ Cont comp action ledger ∧
            PkgSig srcBundle src srcPkg ∧ PkgSig tgtBundle tgt tgtPkg := by
  intro row
  have graphUnary : UnaryHistory graph :=
    unary_cont_closed row.left row.right.left row.right.right.left
  have invGraphUnary : UnaryHistory invGraph :=
    unary_cont_closed row.right.left row.left row.right.right.right.left
  have compUnary : UnaryHistory comp :=
    unary_cont_closed graphUnary invGraphUnary row.right.right.right.right.left
  have actionUnary : UnaryHistory action :=
    unary_cont_closed row.left graphUnary row.right.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed compUnary actionUnary row.right.right.right.right.right.right.left
  exact And.intro graphUnary
    (And.intro invGraphUnary
      (And.intro actionUnary
        (And.intro ledgerUnary
          (And.intro row.right.right.left
            (And.intro row.right.right.right.left
              (And.intro row.right.right.right.right.left
                  (And.intro row.right.right.right.right.right.left
                    (And.intro row.right.right.right.right.right.right.left
                      row.right.right.right.right.right.right.right))))))))

theorem PermutationBijectionSourceRow_action_ledger_transport [AskSetup] [PackageSetup]
    {src tgt graph invGraph comp action ledger action' ledger' : BHist}
    {srcBundle tgtBundle : ProbeBundle ProbeName} {srcPkg tgtPkg : Pkg} :
    PermutationBijectionSourceRow src tgt graph invGraph comp action ledger srcBundle
        tgtBundle srcPkg tgtPkg ->
      hsame action action' -> Cont src graph action' -> Cont comp action' ledger' ->
        PermutationBijectionSourceRow src tgt graph invGraph comp action' ledger' srcBundle
            tgtBundle srcPkg tgtPkg ∧
          hsame ledger ledger' ∧ UnaryHistory action' ∧ UnaryHistory ledger' := by
  intro row sameAction actionCont' ledgerCont'
  have surface := PermutationBijectionSourceRow_carrier_surface row
  have compUnary : UnaryHistory comp :=
    unary_cont_closed surface.left surface.right.left surface.right.right.right.right.right.right.left
  have actionUnary' : UnaryHistory action' :=
    unary_cont_closed row.left surface.left actionCont'
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed compUnary actionUnary' ledgerCont'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame (hsame_refl comp) sameAction
      row.right.right.right.right.right.right.left ledgerCont'
  exact And.intro
    (And.intro row.left
      (And.intro row.right.left
        (And.intro row.right.right.left
          (And.intro row.right.right.right.left
            (And.intro row.right.right.right.right.left
              (And.intro actionCont'
                (And.intro ledgerCont'
                  row.right.right.right.right.right.right.right)))))))
    (And.intro sameLedger (And.intro actionUnary' ledgerUnary'))

theorem PermutationBijectionSourceRow_endpoint_package_hsame_transport [AskSetup] [PackageSetup]
    {src tgt graph invGraph comp action ledger src' tgt' graph' invGraph' comp' action'
      ledger' : BHist}
    {srcBundle tgtBundle : ProbeBundle ProbeName} {srcPkg tgtPkg : Pkg} :
    PermutationBijectionSourceRow src tgt graph invGraph comp action ledger srcBundle
        tgtBundle srcPkg tgtPkg ->
      hsame src src' -> hsame tgt tgt' -> PkgSig srcBundle src' srcPkg ->
        PkgSig tgtBundle tgt' tgtPkg -> Cont src' tgt' graph' ->
          Cont tgt' src' invGraph' -> Cont graph' invGraph' comp' ->
            Cont src' graph' action' -> Cont comp' action' ledger' ->
              PermutationBijectionSourceRow src' tgt' graph' invGraph' comp' action'
                  ledger' srcBundle tgtBundle srcPkg tgtPkg ∧
                hsame graph graph' ∧ hsame invGraph invGraph' ∧ hsame comp comp' ∧
                  hsame action action' ∧ hsame ledger ledger' := by
  intro row sameSrc sameTgt srcPkg' tgtPkg' graphCont' invGraphCont' compCont'
    actionCont' ledgerCont'
  have srcUnary' : UnaryHistory src' :=
    unary_transport row.left sameSrc
  have tgtUnary' : UnaryHistory tgt' :=
    unary_transport row.right.left sameTgt
  have sameGraph : hsame graph graph' :=
    cont_respects_hsame sameSrc sameTgt row.right.right.left graphCont'
  have sameInvGraph : hsame invGraph invGraph' :=
    cont_respects_hsame sameTgt sameSrc row.right.right.right.left invGraphCont'
  have sameComp : hsame comp comp' :=
    cont_respects_hsame sameGraph sameInvGraph row.right.right.right.right.left compCont'
  have sameAction : hsame action action' :=
    cont_respects_hsame sameSrc sameGraph row.right.right.right.right.right.left actionCont'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameComp sameAction row.right.right.right.right.right.right.left
      ledgerCont'
  exact And.intro
    (And.intro srcUnary'
      (And.intro tgtUnary'
        (And.intro graphCont'
          (And.intro invGraphCont'
            (And.intro compCont'
              (And.intro actionCont'
                (And.intro ledgerCont' (And.intro srcPkg' tgtPkg'))))))))
    (And.intro sameGraph
      (And.intro sameInvGraph
        (And.intro sameComp (And.intro sameAction sameLedger))))

end BEDC.Derived.PermutationUp
