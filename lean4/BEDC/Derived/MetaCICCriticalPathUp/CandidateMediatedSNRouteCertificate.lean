import BEDC.Derived.MetaCICCriticalPathUp.OpenPhase
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateMediatedSNRoute_semantic_name_certificate
    [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal confluenceRead socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName confluenceRead →
        Cont handoff obstruction socketRead →
          PkgSig bundle confluenceRead pkg →
            PkgSig bundle socketRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row confluenceRead ∨ hsame row socketRead ∨
                      hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                        hsame row realSeal) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row strongNorm ∨ hsame row normalForm ∨
                      hsame row confluenceRead ∨ hsame row socketRead ∨
                        hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                          hsame row realSeal)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle confluenceRead pkg ∧
                      PkgSig bundle socketRead pkg ∧ PkgSig bundle realSeal pkg)
                  hsame ∧
                UnaryHistory confluenceRead ∧ UnaryHistory socketRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalNameConfluence handoffObstructionSocket confluencePkg
    socketPkg
  obtain ⟨packet, dyadicUnary, streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨strongNormUnary, normalFormUnary, obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have confluenceUnary : UnaryHistory confluenceRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalNameConfluence
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed handoffUnary obstructionUnary handoffObstructionSocket
  have sourceConfluence :
      (fun row : BHist =>
        (hsame row confluenceRead ∨ hsame row socketRead ∨ hsame row dyadic ∨
          hsame row stream ∨ hsame row regseq ∨ hsame row realSeal) ∧
          UnaryHistory row) confluenceRead := by
    exact ⟨Or.inl (hsame_refl confluenceRead), confluenceUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row confluenceRead ∨ hsame row socketRead ∨ hsame row dyadic ∨
              hsame row stream ∨ hsame row regseq ∨ hsame row realSeal) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row confluenceRead ∨
              hsame row socketRead ∨ hsame row dyadic ∨ hsame row stream ∨
                hsame row regseq ∨ hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle confluenceRead pkg ∧
              PkgSig bundle socketRead pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro confluenceRead sourceConfluence
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
        constructor
        · cases source.left with
          | inl sameConfluence =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameConfluence)
          | inr rest =>
              cases rest with
              | inl sameSocket =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameSocket))
              | inr rest =>
                  cases rest with
                  | inl sameDyadic =>
                      exact
                        Or.inr
                          (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameDyadic)))
                  | inr rest =>
                      cases rest with
                      | inl sameStream =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inl (hsame_trans (hsame_symm sameRows) sameStream))))
                      | inr rest =>
                          cases rest with
                          | inl sameRegseq =>
                              exact
                                Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inl
                                          (hsame_trans (hsame_symm sameRows) sameRegseq)))))
                          | inr sameRealSeal =>
                              exact
                                Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (hsame_trans (hsame_symm sameRows)
                                            sameRealSeal)))))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameConfluence =>
          exact Or.inr (Or.inr (Or.inl sameConfluence))
      | inr rest =>
          cases rest with
          | inl sameSocket =>
              exact Or.inr (Or.inr (Or.inr (Or.inl sameSocket)))
          | inr rest =>
              cases rest with
              | inl sameDyadic =>
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameDyadic))))
              | inr rest =>
                  cases rest with
                  | inl sameStream =>
                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameStream)))))
                  | inr rest =>
                      cases rest with
                      | inl sameRegseq =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr (Or.inl sameRegseq))))))
                      | inr sameRealSeal =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr (Or.inr sameRealSeal))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, confluencePkg, socketPkg, realSealPkg⟩
  }
  exact ⟨cert, confluenceUnary, socketUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
