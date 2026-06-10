import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathResidualDiamondL10LocalityObstruction [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName dyadic stream regseq realSeal candidateRead frontierRead socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction handoff
        dischargeSocket transport route provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont route localName candidateRead →
        Cont candidateRead handoff frontierRead →
          Cont frontierRead obstruction socketRead →
            PkgSig bundle socketRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                        hsame row realSeal) ∧
                      UnaryHistory row)
                  (fun row : BHist =>
                    hsame row candidateRead ∨ hsame row frontierRead ∨
                      hsame row socketRead ∨ hsame row dyadic ∨ hsame row stream ∨
                        hsame row regseq ∨ hsame row realSeal)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle realSeal pkg ∧
                      PkgSig bundle socketRead pkg)
                  hsame ∧
                UnaryHistory socketRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger routeLocalNameCandidate candidateHandoffFrontier frontierObstructionSocket
    socketPkg
  obtain ⟨packet, dyadicUnary, streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
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
  have sourceDyadic :
      (fun row : BHist =>
        (hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨ hsame row realSeal) ∧
          UnaryHistory row) dyadic := by
    exact ⟨Or.inl (hsame_refl dyadic), dyadicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                hsame row realSeal) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row frontierRead ∨ hsame row socketRead ∨
              hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨ hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle realSeal pkg ∧ PkgSig bundle socketRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro dyadic sourceDyadic
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
            | inl sameDyadic =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameDyadic)
            | inr rest =>
                cases rest with
                | inl sameStream =>
                    exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameStream))
                | inr rest =>
                    cases rest with
                    | inl sameRegseq =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inl (hsame_trans (hsame_symm sameRows) sameRegseq)))
                    | inr sameRealSeal =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inr (hsame_trans (hsame_symm sameRows) sameRealSeal)))
            ,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameDyadic =>
          exact Or.inr (Or.inr (Or.inr (Or.inl sameDyadic)))
      | inr rest =>
          cases rest with
          | inl sameStream =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameStream))))
          | inr rest =>
              cases rest with
              | inl sameRegseq =>
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameRegseq)))))
              | inr sameRealSeal =>
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameRealSeal)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, realSealPkg, socketPkg⟩
  }
  exact ⟨cert, socketUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
