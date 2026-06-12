import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateResidualBudgetInterface [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName sourceLedger candidateResidual budgetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName sourceLedger →
        Cont sourceLedger dischargeSocket candidateResidual →
          Cont candidateResidual obstruction budgetRead →
            PkgSig bundle budgetRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row route ∨ hsame row localName ∨ hsame row sourceLedger ∨
                      hsame row dischargeSocket ∨ hsame row candidateResidual ∨
                        hsame row obstruction ∨ hsame row budgetRead)
                  (fun _row : BHist =>
                    PkgSig bundle budgetRead pkg ∧ PkgSig bundle provenance pkg ∧
                      Cont strongNorm normalForm route ∧
                        Cont handoff obstruction dischargeSocket)
                  hsame ∧
                UnaryHistory sourceLedger ∧ UnaryHistory candidateResidual ∧
                  UnaryHistory budgetRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet routeLocalNameSource sourceSocketCandidate candidateObstructionBudget
    budgetPkg
  obtain ⟨strongNormUnary, normalFormUnary, obstructionUnary, handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, provenanceUnary, localNameUnary,
    strongNormNormalFormRoute, handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have sourceLedgerUnary : UnaryHistory sourceLedger :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameSource
  have candidateResidualUnary : UnaryHistory candidateResidual :=
    unary_cont_closed sourceLedgerUnary dischargeSocketUnary sourceSocketCandidate
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed candidateResidualUnary obstructionUnary candidateObstructionBudget
  have sourceBudget :
      (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row) budgetRead := by
    exact ⟨hsame_refl budgetRead, budgetReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row route ∨ hsame row localName ∨ hsame row sourceLedger ∨
              hsame row dischargeSocket ∨ hsame row candidateResidual ∨
                hsame row obstruction ∨ hsame row budgetRead)
          (fun _row : BHist =>
            PkgSig bundle budgetRead pkg ∧ PkgSig bundle provenance pkg ∧
              Cont strongNorm normalForm route ∧ Cont handoff obstruction dischargeSocket)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro budgetRead sourceBudget
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
      intro _row _source
      exact
        ⟨budgetPkg, provenancePkg, strongNormNormalFormRoute, handoffObstructionSocket⟩
  }
  exact
    ⟨cert, sourceLedgerUnary, candidateResidualUnary, budgetReadUnary, provenancePkg⟩

theorem MetaCICCriticalPathCandidateResidualDischargeBudget [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName sourceLedger candidateResidual budgetRead dischargeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName sourceLedger →
        Cont sourceLedger dischargeSocket candidateResidual →
          Cont candidateResidual obstruction budgetRead →
            Cont budgetRead transport dischargeRead →
              PkgSig bundle dischargeRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row dischargeRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row sourceLedger ∨ hsame row candidateResidual ∨
                        hsame row budgetRead ∨ hsame row dischargeRead ∨
                          hsame row obstruction ∨ hsame row transport)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle dischargeRead pkg ∧
                        Cont route localName sourceLedger ∧
                          Cont sourceLedger dischargeSocket candidateResidual ∧
                            Cont candidateResidual obstruction budgetRead ∧
                              Cont budgetRead transport dischargeRead)
                    hsame ∧
                  UnaryHistory sourceLedger ∧ UnaryHistory candidateResidual ∧
                    UnaryHistory budgetRead ∧ UnaryHistory dischargeRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet routeLocalNameSource sourceSocketCandidate candidateObstructionBudget
    budgetTransportDischarge dischargePkg
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _handoffUnary,
    dischargeSocketUnary, transportUnary, routeUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    _provenancePkg⟩ := packet
  have sourceLedgerUnary : UnaryHistory sourceLedger :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameSource
  have candidateResidualUnary : UnaryHistory candidateResidual :=
    unary_cont_closed sourceLedgerUnary dischargeSocketUnary sourceSocketCandidate
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed candidateResidualUnary obstructionUnary candidateObstructionBudget
  have dischargeReadUnary : UnaryHistory dischargeRead :=
    unary_cont_closed budgetReadUnary transportUnary budgetTransportDischarge
  have sourceDischarge :
      (fun row : BHist => hsame row dischargeRead ∧ UnaryHistory row) dischargeRead := by
    exact ⟨hsame_refl dischargeRead, dischargeReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row dischargeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sourceLedger ∨ hsame row candidateResidual ∨
              hsame row budgetRead ∨ hsame row dischargeRead ∨
                hsame row obstruction ∨ hsame row transport)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle dischargeRead pkg ∧
              Cont route localName sourceLedger ∧
                Cont sourceLedger dischargeSocket candidateResidual ∧
                  Cont candidateResidual obstruction budgetRead ∧
                    Cont budgetRead transport dischargeRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro dischargeRead sourceDischarge
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
      exact Or.inr (Or.inr (Or.inr (Or.inl source.left)))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, dischargePkg, routeLocalNameSource, sourceSocketCandidate,
          candidateObstructionBudget, budgetTransportDischarge⟩
  }
  exact
    ⟨cert, sourceLedgerUnary, candidateResidualUnary, budgetReadUnary, dischargeReadUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
