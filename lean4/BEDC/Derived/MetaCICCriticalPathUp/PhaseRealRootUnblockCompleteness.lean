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

theorem MetaCICCriticalPathPhaseRealRootUnblockCompleteness [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      (hsame sourceRead dyadic ∨ hsame sourceRead stream ∨ hsame sourceRead regseq ∨
          hsame sourceRead realSeal) →
        SemanticNameCert
            (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                hsame row realSeal)
            (fun row : BHist => PkgSig bundle realSeal pkg ∧ hsame row sourceRead)
            hsame ∧
          UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory regseq ∧
            UnaryHistory realSeal ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro ledger sourceCase
  obtain ⟨_packet, dyadicUnary, streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  have sourceReadUnary : UnaryHistory sourceRead := by
    cases sourceCase with
    | inl sourceDyadic =>
        exact unary_transport dyadicUnary (hsame_symm sourceDyadic)
    | inr rest =>
        cases rest with
        | inl sourceStream =>
            exact unary_transport streamUnary (hsame_symm sourceStream)
        | inr rest =>
            cases rest with
            | inl sourceRegseq =>
                exact unary_transport regseqUnary (hsame_symm sourceRegseq)
            | inr sourceRealSeal =>
                exact unary_transport realSealUnary (hsame_symm sourceRealSeal)
  have sourceWitness :
      (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row) sourceRead := by
    exact ⟨hsame_refl sourceRead, sourceReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨ hsame row realSeal)
          (fun row : BHist => PkgSig bundle realSeal pkg ∧ hsame row sourceRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceRead sourceWitness
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
      cases sourceCase with
      | inl sourceDyadic =>
          exact Or.inl (hsame_trans source.left sourceDyadic)
      | inr rest =>
          cases rest with
          | inl sourceStream =>
              exact Or.inr (Or.inl (hsame_trans source.left sourceStream))
          | inr rest =>
              cases rest with
              | inl sourceRegseq =>
                  exact Or.inr (Or.inr (Or.inl (hsame_trans source.left sourceRegseq)))
              | inr sourceRealSeal =>
                  exact Or.inr (Or.inr (Or.inr (hsame_trans source.left sourceRealSeal)))
    ledger_sound := by
      intro _row source
      exact ⟨realSealPkg, source.left⟩
  }
  exact ⟨cert, dyadicUnary, streamUnary, regseqUnary, realSealUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
