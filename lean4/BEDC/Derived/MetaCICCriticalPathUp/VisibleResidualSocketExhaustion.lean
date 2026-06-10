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

theorem MetaCICCriticalPathVisibleResidualSocketExhaustion [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName sourceLedger candidateResidual budgetRead diamondRead checkerRead socketRead :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      Cont route localName sourceLedger ->
        Cont sourceLedger dischargeSocket candidateResidual ->
          Cont candidateResidual obstruction budgetRead ->
            Cont budgetRead normalForm diamondRead ->
              Cont diamondRead transport checkerRead ->
                Cont checkerRead dischargeSocket socketRead ->
                  PkgSig bundle socketRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row socketRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row candidateResidual ∨ hsame row budgetRead ∨
                            hsame row diamondRead ∨ hsame row checkerRead ∨
                              hsame row socketRead ∨ hsame row dischargeSocket ∨
                                hsame row obstruction)
                        (fun row : BHist =>
                          UnaryHistory row ∧ PkgSig bundle socketRead pkg ∧
                            PkgSig bundle provenance pkg)
                        hsame ∧
                      UnaryHistory candidateResidual ∧ UnaryHistory budgetRead ∧
                        UnaryHistory diamondRead ∧ UnaryHistory checkerRead ∧
                          UnaryHistory socketRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro packet routeLocalNameSource sourceSocketCandidate candidateObstructionBudget
    budgetNormalDiamond diamondTransportChecker checkerSocketRead socketPkg
  obtain ⟨_strongNormUnary, normalFormUnary, obstructionUnary, _handoffUnary,
    dischargeSocketUnary, transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have sourceUnary : UnaryHistory sourceLedger :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameSource
  have candidateUnary : UnaryHistory candidateResidual :=
    unary_cont_closed sourceUnary dischargeSocketUnary sourceSocketCandidate
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed candidateUnary obstructionUnary candidateObstructionBudget
  have diamondUnary : UnaryHistory diamondRead :=
    unary_cont_closed budgetUnary normalFormUnary budgetNormalDiamond
  have checkerUnary : UnaryHistory checkerRead :=
    unary_cont_closed diamondUnary transportUnary diamondTransportChecker
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed checkerUnary dischargeSocketUnary checkerSocketRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row socketRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateResidual ∨ hsame row budgetRead ∨ hsame row diamondRead ∨
              hsame row checkerRead ∨ hsame row socketRead ∨ hsame row dischargeSocket ∨
                hsame row obstruction)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle socketRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro socketRead ⟨hsame_refl socketRead, socketUnary⟩
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
      exact ⟨source.right, socketPkg, provenancePkg⟩
  }
  exact ⟨cert, candidateUnary, budgetUnary, diamondUnary, checkerUnary, socketUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
