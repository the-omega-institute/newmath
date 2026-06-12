import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathResidualBudgetFactorization [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName dyadic stream regseq realSeal candidateRead frontierRead socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction handoff
        dischargeSocket transport route provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont route localName candidateRead →
        Cont candidateRead handoff frontierRead →
          Cont frontierRead obstruction socketRead →
            PkgSig bundle frontierRead pkg →
              PkgSig bundle socketRead pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row candidateRead ∨ hsame row frontierRead ∨
                          hsame row socketRead) ∧
                        UnaryHistory row)
                    (fun row : BHist =>
                      hsame row route ∨ hsame row candidateRead ∨ hsame row frontierRead ∨
                        hsame row socketRead ∨ hsame row dyadic ∨ hsame row stream ∨
                          hsame row regseq ∨ hsame row realSeal)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont route localName candidateRead ∧
                        Cont candidateRead handoff frontierRead ∧
                          Cont frontierRead obstruction socketRead ∧
                            PkgSig bundle frontierRead pkg ∧ PkgSig bundle socketRead pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger routeLocalNameCandidate candidateHandoffFrontier frontierObstructionSocket
    frontierPkg socketPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, _realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameCandidate
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed candidateUnary handoffUnary candidateHandoffFrontier
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed frontierUnary obstructionUnary frontierObstructionSocket
  have sourceCandidate :
      (fun row : BHist =>
        (hsame row candidateRead ∨ hsame row frontierRead ∨ hsame row socketRead) ∧
          UnaryHistory row) candidateRead := by
    exact ⟨Or.inl (hsame_refl candidateRead), candidateUnary⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro candidateRead sourceCandidate
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
          ⟨by
            cases source.left with
            | inl sameCandidate =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameCandidate)
            | inr rest =>
                cases rest with
                | inl sameFrontier =>
                    exact
                      Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameFrontier))
                | inr sameSocket =>
                    exact
                      Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameSocket))
            ,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameCandidate =>
          exact Or.inr (Or.inl sameCandidate)
      | inr rest =>
          cases rest with
          | inl sameFrontier =>
              exact Or.inr (Or.inr (Or.inl sameFrontier))
          | inr sameSocket =>
              exact Or.inr (Or.inr (Or.inr (Or.inl sameSocket)))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, routeLocalNameCandidate, candidateHandoffFrontier,
          frontierObstructionSocket, frontierPkg, socketPkg⟩
  }

end BEDC.Derived.MetaCICCriticalPathUp
