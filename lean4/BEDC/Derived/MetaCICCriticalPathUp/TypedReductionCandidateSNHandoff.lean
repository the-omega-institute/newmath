import BEDC.Derived.MetaCICCriticalPathUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICTypedReductionCandidateSNHandoff [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName candidateRead checkerBudget frontierReplay socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont strongNorm normalForm candidateRead →
        Cont candidateRead route checkerBudget →
          Cont checkerBudget handoff frontierReplay →
            Cont handoff obstruction socketRead →
              PkgSig bundle frontierReplay pkg →
                PkgSig bundle socketRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row frontierReplay ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row strongNorm ∨ hsame row normalForm ∨ hsame row route ∨
                          hsame row handoff ∨ hsame row dischargeSocket ∨
                            hsame row checkerBudget ∨ hsame row frontierReplay)
                      (fun row : BHist =>
                        hsame row frontierReplay ∧
                          Cont candidateRead route checkerBudget ∧
                            Cont checkerBudget handoff frontierReplay ∧
                              Cont handoff obstruction socketRead ∧
                                PkgSig bundle frontierReplay pkg ∧
                                  PkgSig bundle socketRead pkg)
                      hsame ∧
                    UnaryHistory candidateRead ∧ UnaryHistory checkerBudget ∧
                      UnaryHistory frontierReplay ∧ UnaryHistory socketRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro packet strongNormalCandidate candidateRouteChecker checkerHandoffFrontier
    handoffObstructionSocket frontierPkg socketPkg
  obtain ⟨strongNormUnary, normalFormUnary, obstructionUnary, handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormRoute, _handoffObstructionSocket,
    _transportLocalName, _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed strongNormUnary normalFormUnary strongNormalCandidate
  have checkerUnary : UnaryHistory checkerBudget :=
    unary_cont_closed candidateUnary routeUnary candidateRouteChecker
  have frontierUnary : UnaryHistory frontierReplay :=
    unary_cont_closed checkerUnary handoffUnary checkerHandoffFrontier
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed handoffUnary obstructionUnary handoffObstructionSocket
  have sourceFrontier :
      (fun row : BHist => hsame row frontierReplay ∧ UnaryHistory row) frontierReplay := by
    exact ⟨hsame_refl frontierReplay, frontierUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row frontierReplay ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row route ∨
              hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row checkerBudget ∨
                hsame row frontierReplay)
          (fun row : BHist =>
            hsame row frontierReplay ∧ Cont candidateRead route checkerBudget ∧
              Cont checkerBudget handoff frontierReplay ∧
                Cont handoff obstruction socketRead ∧ PkgSig bundle frontierReplay pkg ∧
                  PkgSig bundle socketRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro frontierReplay sourceFrontier
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.left, candidateRouteChecker, checkerHandoffFrontier,
          handoffObstructionSocket, frontierPkg, socketPkg⟩
  }
  exact ⟨cert, candidateUnary, checkerUnary, frontierUnary, socketUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
