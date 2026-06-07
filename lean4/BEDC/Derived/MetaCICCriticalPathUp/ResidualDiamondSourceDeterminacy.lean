import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathResidualDiamondSourceDeterminacy [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal residualRead candidateRead sharedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      UnaryHistory residualRead →
        UnaryHistory candidateRead →
          Cont residualRead candidateRead sharedRead →
            PkgSig bundle sharedRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                      hsame row realSeal ∨ hsame row sharedRead) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                      hsame row realSeal ∨ hsame row sharedRead)
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle sharedRead pkg)
                  hsame ∧
                UnaryHistory sharedRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro ledger residualUnary candidateUnary residualCandidateShared sharedPkg
  obtain ⟨_packet, dyadicUnary, streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
  have sharedUnary : UnaryHistory sharedRead :=
    unary_cont_closed residualUnary candidateUnary residualCandidateShared
  have sourceAtShared :
      (fun row : BHist =>
        (hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
          hsame row realSeal ∨ hsame row sharedRead) ∧ UnaryHistory row) sharedRead := by
    exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (hsame_refl sharedRead)))), sharedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row sharedRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row sharedRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle sharedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sharedRead sourceAtShared
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
        intro row other sameRows source
        have patternOther :
            hsame other dyadic ∨ hsame other stream ∨ hsame other regseq ∨
              hsame other realSeal ∨ hsame other sharedRead := by
          cases source.left with
          | inl rowDyadic =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) rowDyadic)
          | inr rest =>
              cases rest with
              | inl rowStream =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowStream))
              | inr rest =>
                  cases rest with
                  | inl rowRegseq =>
                      exact
                        Or.inr
                          (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowRegseq)))
                  | inr rest =>
                      cases rest with
                      | inl rowRealSeal =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inl
                                    (hsame_trans (hsame_symm sameRows) rowRealSeal))))
                      | inr rowShared =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (hsame_trans (hsame_symm sameRows) rowShared))))
        exact ⟨patternOther, unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sharedPkg⟩
  }
  exact ⟨cert, sharedUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
