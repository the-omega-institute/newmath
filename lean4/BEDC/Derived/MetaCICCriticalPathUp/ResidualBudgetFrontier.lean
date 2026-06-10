import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathResidualBudgetFrontier [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName closedRead residualRead mediatedRead frontierRead checkerRead
      decidabilityRead sourceLedger candidateResidual budgetRead combinedRead publicRead :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont transport route closedRead →
        Cont handoff dischargeSocket residualRead →
          Cont strongNorm normalForm mediatedRead →
            Cont closedRead residualRead frontierRead →
              Cont frontierRead transport checkerRead →
                Cont checkerRead handoff decidabilityRead →
                  Cont route localName sourceLedger →
                    Cont sourceLedger dischargeSocket candidateResidual →
                      Cont candidateResidual obstruction budgetRead →
                        Cont route handoff combinedRead →
                          Cont combinedRead decidabilityRead publicRead →
                            PkgSig bundle publicRead pkg →
                              SemanticNameCert
                                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row frontierRead ∨ hsame row checkerRead ∨
                                      hsame row decidabilityRead ∨ hsame row budgetRead ∨
                                        hsame row combinedRead ∨ hsame row publicRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧
                                      Cont combinedRead decidabilityRead publicRead ∧
                                        PkgSig bundle publicRead pkg)
                                  hsame ∧
                                UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet transportRouteClosed handoffSocketResidual strongNormalMediated
    closedResidualFrontier frontierTransportChecker checkerHandoffDecidability
    routeLocalNameSource sourceSocketCandidate candidateObstructionBudget routeHandoffCombined
    combinedDecidabilityPublic publicPkg
  obtain ⟨strongNormUnary, normalFormUnary, obstructionUnary, handoffUnary,
    dischargeSocketUnary, transportUnary, routeUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    _provenancePkg⟩ := packet
  have closedUnary : UnaryHistory closedRead :=
    unary_cont_closed transportUnary routeUnary transportRouteClosed
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed handoffUnary dischargeSocketUnary handoffSocketResidual
  have mediatedUnary : UnaryHistory mediatedRead :=
    unary_cont_closed strongNormUnary normalFormUnary strongNormalMediated
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed closedUnary residualUnary closedResidualFrontier
  have checkerUnary : UnaryHistory checkerRead :=
    unary_cont_closed frontierUnary transportUnary frontierTransportChecker
  have decidabilityUnary : UnaryHistory decidabilityRead :=
    unary_cont_closed checkerUnary handoffUnary checkerHandoffDecidability
  have sourceLedgerUnary : UnaryHistory sourceLedger :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameSource
  have candidateResidualUnary : UnaryHistory candidateResidual :=
    unary_cont_closed sourceLedgerUnary dischargeSocketUnary sourceSocketCandidate
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed candidateResidualUnary obstructionUnary candidateObstructionBudget
  have combinedUnary : UnaryHistory combinedRead :=
    unary_cont_closed routeUnary handoffUnary routeHandoffCombined
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed combinedUnary decidabilityUnary combinedDecidabilityPublic
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row frontierRead ∨ hsame row checkerRead ∨ hsame row decidabilityRead ∨
              hsame row budgetRead ∨ hsame row combinedRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont combinedRead decidabilityRead publicRead ∧
              PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, combinedDecidabilityPublic, publicPkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
