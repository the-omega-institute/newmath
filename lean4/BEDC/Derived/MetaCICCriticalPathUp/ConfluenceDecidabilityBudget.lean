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

theorem MetaCICCriticalPathConfluenceDecidabilityBudget [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal confluenceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg ->
      Cont handoff obstruction confluenceRead ->
        PkgSig bundle confluenceRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row confluenceRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                  hsame row realSeal ∨ hsame row handoff ∨ hsame row obstruction ∨
                    hsame row confluenceRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle confluenceRead pkg ∧
                  PkgSig bundle realSeal pkg ∧ Cont handoff obstruction confluenceRead)
              hsame ∧
            UnaryHistory confluenceRead ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger handoffObstructionConfluence confluencePkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, _realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, _continuationUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have confluenceUnary : UnaryHistory confluenceRead :=
    unary_cont_closed handoffUnary obstructionUnary handoffObstructionConfluence
  have sourceConfluence :
      (fun row : BHist => hsame row confluenceRead ∧ UnaryHistory row)
        confluenceRead := by
    exact ⟨hsame_refl confluenceRead, confluenceUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row confluenceRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row handoff ∨ hsame row obstruction ∨
                hsame row confluenceRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle confluenceRead pkg ∧
              PkgSig bundle realSeal pkg ∧ Cont handoff obstruction confluenceRead)
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, confluencePkg, realSealPkg, handoffObstructionConfluence⟩
  }
  exact ⟨cert, confluenceUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
