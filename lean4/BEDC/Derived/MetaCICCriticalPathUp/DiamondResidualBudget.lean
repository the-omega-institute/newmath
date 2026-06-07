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

theorem MetaCICCriticalPathDiamondResidualBudget [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName checkerBudget combinedRead decidabilityRead residualBudget diamondRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket transport
        route provenance localName bundle pkg →
      Cont route handoff checkerBudget →
        Cont checkerBudget dischargeSocket combinedRead →
          Cont combinedRead obstruction decidabilityRead →
            Cont decidabilityRead transport residualBudget →
              Cont residualBudget normalForm diamondRead →
                PkgSig bundle diamondRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row diamondRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row checkerBudget ∨ hsame row combinedRead ∨
                          hsame row decidabilityRead ∨ hsame row residualBudget ∨
                            hsame row diamondRead ∨ hsame row provenance)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle diamondRead pkg ∧
                          PkgSig bundle provenance pkg)
                      hsame ∧
                    UnaryHistory checkerBudget ∧ UnaryHistory combinedRead ∧
                      UnaryHistory decidabilityRead ∧ UnaryHistory residualBudget ∧
                        UnaryHistory diamondRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet routeHandoffChecker checkerSocketCombined combinedObstructionDecidability
    decidabilityTransportResidual residualNormalDiamond diamondPkg
  obtain ⟨_strongNormUnary, normalFormUnary, obstructionUnary, handoffUnary,
    dischargeSocketUnary, transportUnary, routeUnary, provenanceUnary, _localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have checkerUnary : UnaryHistory checkerBudget :=
    unary_cont_closed routeUnary handoffUnary routeHandoffChecker
  have combinedUnary : UnaryHistory combinedRead :=
    unary_cont_closed checkerUnary dischargeSocketUnary checkerSocketCombined
  have decidabilityUnary : UnaryHistory decidabilityRead :=
    unary_cont_closed combinedUnary obstructionUnary combinedObstructionDecidability
  have residualUnary : UnaryHistory residualBudget :=
    unary_cont_closed decidabilityUnary transportUnary decidabilityTransportResidual
  have diamondUnary : UnaryHistory diamondRead :=
    unary_cont_closed residualUnary normalFormUnary residualNormalDiamond
  have sourceDiamond :
      (fun row : BHist => hsame row diamondRead ∧ UnaryHistory row) diamondRead := by
    exact ⟨hsame_refl diamondRead, diamondUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row diamondRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row checkerBudget ∨ hsame row combinedRead ∨
              hsame row decidabilityRead ∨ hsame row residualBudget ∨
                hsame row diamondRead ∨ hsame row provenance)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle diamondRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro diamondRead sourceDiamond
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, diamondPkg, provenancePkg⟩
  }
  exact
    ⟨cert, checkerUnary, combinedUnary, decidabilityUnary, residualUnary, diamondUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
