import BEDC.Derived.MetaCICCriticalPathUp.Core
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathVisibleResidualLocalDecidabilityBudget [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName sourceLedger candidateResidual budgetRead diamondRead checkerRead localRead
      decidabilityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      Cont route localName sourceLedger ->
        Cont sourceLedger dischargeSocket candidateResidual ->
          Cont candidateResidual obstruction budgetRead ->
            Cont budgetRead normalForm diamondRead ->
              Cont diamondRead transport checkerRead ->
                Cont checkerRead localName localRead ->
                  Cont localRead obstruction decidabilityRead ->
                    PkgSig bundle decidabilityRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row decidabilityRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row candidateResidual ∨ hsame row budgetRead ∨
                              hsame row diamondRead ∨ hsame row checkerRead ∨
                                hsame row localRead ∨ hsame row decidabilityRead ∨
                                  hsame row obstruction ∨ hsame row dischargeSocket)
                          (fun row : BHist =>
                            UnaryHistory row ∧ PkgSig bundle decidabilityRead pkg ∧
                              PkgSig bundle provenance pkg ∧
                                Cont localRead obstruction decidabilityRead)
                          hsame ∧
                        UnaryHistory localRead ∧ UnaryHistory decidabilityRead ∧
                          UnaryHistory checkerRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle Pkg SemanticNameCert hsame
  intro packet routeLocalNameSource sourceSocketCandidate candidateObstructionBudget
    budgetNormalDiamond diamondTransportChecker checkerLocalRead localObstructionDecidable
    decidabilityPkg
  obtain ⟨_strongNormUnary, normalFormUnary, obstructionUnary, _handoffUnary,
    dischargeSocketUnary, transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have sourceLedgerUnary : UnaryHistory sourceLedger :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameSource
  have candidateUnary : UnaryHistory candidateResidual :=
    unary_cont_closed sourceLedgerUnary dischargeSocketUnary sourceSocketCandidate
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed candidateUnary obstructionUnary candidateObstructionBudget
  have diamondUnary : UnaryHistory diamondRead :=
    unary_cont_closed budgetUnary normalFormUnary budgetNormalDiamond
  have checkerUnary : UnaryHistory checkerRead :=
    unary_cont_closed diamondUnary transportUnary diamondTransportChecker
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed checkerUnary localNameUnary checkerLocalRead
  have decidabilityUnary : UnaryHistory decidabilityRead :=
    unary_cont_closed localUnary obstructionUnary localObstructionDecidable
  have sourceDecidability :
      (fun row : BHist => hsame row decidabilityRead ∧ UnaryHistory row)
        decidabilityRead := by
    exact ⟨hsame_refl decidabilityRead, decidabilityUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row decidabilityRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateResidual ∨ hsame row budgetRead ∨
              hsame row diamondRead ∨ hsame row checkerRead ∨ hsame row localRead ∨
                hsame row decidabilityRead ∨ hsame row obstruction ∨
                  hsame row dischargeSocket)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle decidabilityRead pkg ∧
              PkgSig bundle provenance pkg ∧ Cont localRead obstruction decidabilityRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro decidabilityRead sourceDecidability
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, decidabilityPkg, provenancePkg, localObstructionDecidable⟩
  }
  exact ⟨cert, localUnary, decidabilityUnary, checkerUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
