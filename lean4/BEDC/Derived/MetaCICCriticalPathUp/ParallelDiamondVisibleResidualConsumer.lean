import BEDC.Derived.MetaCICCriticalPathUp.CandidateDischargeVisibleResidualRoute

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathParallelDiamondVisibleResidualConsumer [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName sourceLedger candidateResidual budgetRead diamondRead checkerRead
      visibleRead confluenceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName sourceLedger →
        Cont sourceLedger dischargeSocket candidateResidual →
          Cont candidateResidual obstruction budgetRead →
            Cont budgetRead normalForm diamondRead →
              Cont diamondRead transport checkerRead →
                Cont checkerRead provenance visibleRead →
                  Cont visibleRead handoff confluenceRead →
                    PkgSig bundle confluenceRead pkg →
                      SemanticNameCert
                          (fun row : BHist =>
                            (hsame row visibleRead ∨ hsame row confluenceRead ∨
                              hsame row diamondRead ∨ hsame row dischargeSocket) ∧
                              UnaryHistory row)
                          (fun row : BHist =>
                            hsame row candidateResidual ∨ hsame row budgetRead ∨
                              hsame row diamondRead ∨ hsame row checkerRead ∨
                                hsame row visibleRead ∨ hsame row confluenceRead ∨
                                  hsame row dischargeSocket ∨ hsame row obstruction)
                          (fun row : BHist =>
                            UnaryHistory row ∧ PkgSig bundle confluenceRead pkg ∧
                              PkgSig bundle provenance pkg)
                          hsame ∧
                        UnaryHistory confluenceRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle Pkg SemanticNameCert hsame
  intro packet routeLocalSource sourceSocketCandidate candidateObstructionBudget
    budgetNormalDiamond diamondTransportChecker checkerProvenanceVisible
    visibleHandoffConfluence confluencePkg
  obtain ⟨_strongNormUnary, normalFormUnary, obstructionUnary, handoffUnary,
    dischargeSocketUnary, transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have sourceLedgerUnary : UnaryHistory sourceLedger :=
    unary_cont_closed routeUnary localNameUnary routeLocalSource
  have candidateUnary : UnaryHistory candidateResidual :=
    unary_cont_closed sourceLedgerUnary dischargeSocketUnary sourceSocketCandidate
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed candidateUnary obstructionUnary candidateObstructionBudget
  have diamondUnary : UnaryHistory diamondRead :=
    unary_cont_closed budgetUnary normalFormUnary budgetNormalDiamond
  have checkerUnary : UnaryHistory checkerRead :=
    unary_cont_closed diamondUnary transportUnary diamondTransportChecker
  have visibleUnary : UnaryHistory visibleRead :=
    unary_cont_closed checkerUnary provenanceUnary checkerProvenanceVisible
  have confluenceUnary : UnaryHistory confluenceRead :=
    unary_cont_closed visibleUnary handoffUnary visibleHandoffConfluence
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row visibleRead ∨ hsame row confluenceRead ∨ hsame row diamondRead ∨
              hsame row dischargeSocket) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateResidual ∨ hsame row budgetRead ∨ hsame row diamondRead ∨
              hsame row checkerRead ∨ hsame row visibleRead ∨ hsame row confluenceRead ∨
                hsame row dischargeSocket ∨ hsame row obstruction)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle confluenceRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro confluenceRead
          ⟨Or.inr (Or.inl (hsame_refl confluenceRead)), confluenceUnary⟩
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameVisible =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameVisible))))
      | inr rest =>
          cases rest with
          | inl sameConfluence =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr (Or.inl sameConfluence)))))
          | inr rest =>
              cases rest with
              | inl sameDiamond =>
                  exact Or.inr (Or.inr (Or.inl sameDiamond))
              | inr sameSocket =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr (Or.inr (Or.inl sameSocket))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, confluencePkg, provenancePkg⟩
  }
  exact ⟨cert, confluenceUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
