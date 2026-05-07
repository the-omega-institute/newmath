import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PermutationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem PermutationBijectionSourceRow_composition_action_ledger_scope [AskSetup] [PackageSetup]
    {src tgt graph invGraph comp action ledger : BHist}
    {srcBundle tgtBundle : ProbeBundle ProbeName} {srcPkg tgtPkg : Pkg} :
    PermutationBijectionSourceRow src tgt graph invGraph comp action ledger srcBundle tgtBundle
        srcPkg tgtPkg ->
      hsame comp (append graph invGraph) ∧ hsame action (append src graph) ∧
        hsame ledger (append (append graph invGraph) (append src graph)) := by
  intro row
  have compScope : hsame comp (append graph invGraph) :=
    row.right.right.right.right.left
  have actionScope : hsame action (append src graph) :=
    row.right.right.right.right.right.left
  have ledgerScope : hsame ledger (append comp action) :=
    row.right.right.right.right.right.right.left
  have expandedLedger :
      hsame (append comp action) (append (append graph invGraph) (append src graph)) := by
    cases compScope
    cases actionScope
    exact hsame_refl (append (append graph invGraph) (append src graph))
  exact And.intro compScope (And.intro actionScope (hsame_trans ledgerScope expandedLedger))

theorem PermutationBijectionSourceRow_semantic_name_certificate [AskSetup] [PackageSetup]
    {src tgt graph invGraph comp action ledger : BHist}
    {srcBundle tgtBundle : ProbeBundle ProbeName} {srcPkg tgtPkg : Pkg} :
    PermutationBijectionSourceRow src tgt graph invGraph comp action ledger srcBundle
      tgtBundle srcPkg tgtPkg ->
      SemanticNameCert
        (fun endpoint : BHist =>
          PermutationBijectionSourceRow src tgt graph invGraph comp action endpoint srcBundle
            tgtBundle srcPkg tgtPkg)
        (fun endpoint : BHist =>
          PermutationBijectionSourceRow src tgt graph invGraph comp action endpoint srcBundle
            tgtBundle srcPkg tgtPkg)
        (fun endpoint : BHist =>
          PermutationBijectionSourceRow src tgt graph invGraph comp action endpoint srcBundle
            tgtBundle srcPkg tgtPkg)
        hsame ∧
        hsame comp (append graph invGraph) ∧ hsame action (append src graph) ∧
          hsame ledger (append (append graph invGraph) (append src graph)) := by
  intro row
  have scope := PermutationBijectionSourceRow_composition_action_ledger_scope row
  have cert :
      SemanticNameCert
        (fun endpoint : BHist =>
          PermutationBijectionSourceRow src tgt graph invGraph comp action endpoint srcBundle
            tgtBundle srcPkg tgtPkg)
        (fun endpoint : BHist =>
          PermutationBijectionSourceRow src tgt graph invGraph comp action endpoint srcBundle
            tgtBundle srcPkg tgtPkg)
        (fun endpoint : BHist =>
          PermutationBijectionSourceRow src tgt graph invGraph comp action endpoint srcBundle
            tgtBundle srcPkg tgtPkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro ledger row
      equiv_refl := by
        intro endpoint _endpointRow
        exact hsame_refl endpoint
      equiv_symm := by
        intro endpoint endpoint' sameEndpoint
        exact hsame_symm sameEndpoint
      equiv_trans := by
        intro endpoint endpoint' endpoint'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro endpoint endpoint' sameEndpoint endpointRow
        exact And.intro endpointRow.left
          (And.intro endpointRow.right.left
            (And.intro endpointRow.right.right.left
              (And.intro endpointRow.right.right.right.left
                (And.intro endpointRow.right.right.right.right.left
                  (And.intro endpointRow.right.right.right.right.right.left
                    (And.intro
                      (cont_result_hsame_transport
                        endpointRow.right.right.right.right.right.right.left sameEndpoint)
                      (And.intro endpointRow.right.right.right.right.right.right.right.left
                        endpointRow.right.right.right.right.right.right.right.right)))))))
    }
    pattern_sound := by
      intro endpoint endpointRow
      exact endpointRow
    ledger_sound := by
      intro endpoint endpointRow
      exact endpointRow
  }
  exact And.intro cert scope

theorem PermutationBijectionSourceRow_public_name_certificate [AskSetup] [PackageSetup]
    {src tgt graph invGraph comp action ledger : BHist}
    {srcBundle tgtBundle : ProbeBundle ProbeName} {srcPkg tgtPkg : Pkg} :
    PermutationBijectionSourceRow src tgt graph invGraph comp action ledger srcBundle
        tgtBundle srcPkg tgtPkg ->
      SemanticNameCert
          (fun endpoint : BHist =>
            ∃ actionRow ledgerRow : BHist,
              PermutationBijectionSourceRow src tgt graph invGraph comp actionRow ledgerRow
                srcBundle tgtBundle srcPkg tgtPkg ∧ hsame endpoint ledgerRow)
          (fun endpoint : BHist =>
            ∃ actionRow ledgerRow : BHist,
              PermutationBijectionSourceRow src tgt graph invGraph comp actionRow ledgerRow
                srcBundle tgtBundle srcPkg tgtPkg ∧ hsame endpoint ledgerRow)
          (fun endpoint : BHist =>
            ∃ actionRow ledgerRow : BHist,
              PermutationBijectionSourceRow src tgt graph invGraph comp actionRow ledgerRow
                srcBundle tgtBundle srcPkg tgtPkg ∧ hsame endpoint ledgerRow)
          hsame ∧
        (∀ {tail : BHist}, hsame ledger (BHist.e0 tail) -> False) := by
  intro row
  have surface := PermutationBijectionSourceRow_carrier_surface row
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro ledger
            (Exists.intro action
              (Exists.intro ledger (And.intro row (hsame_refl ledger))))
        equiv_refl := by
          intro endpoint _endpointCarrier
          exact hsame_refl endpoint
        equiv_symm := by
          intro _endpoint leftEndpoint same
          exact hsame_symm same
        equiv_trans := by
          intro _endpoint _middle rightEndpoint sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro endpoint endpoint' sameEndpoint endpointCarrier
          cases endpointCarrier with
          | intro actionRow ledgerWitness =>
              cases ledgerWitness with
              | intro ledgerRow data =>
                  exact Exists.intro actionRow
                    (Exists.intro ledgerRow
                      (And.intro data.left (hsame_trans (hsame_symm sameEndpoint) data.right)))
      }
      pattern_sound := by
        intro _endpoint source
        exact source
      ledger_sound := by
        intro _endpoint source
        exact source
    }
  · intro tail sameLedger
    have zeroUnary : UnaryHistory (BHist.e0 tail) :=
      unary_transport surface.right.right.right.left sameLedger
    exact unary_no_zero_extension zeroUnary

end BEDC.Derived.PermutationUp
