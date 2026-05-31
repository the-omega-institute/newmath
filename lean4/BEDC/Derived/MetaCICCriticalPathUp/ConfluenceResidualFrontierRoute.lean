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

theorem MetaCICCriticalPathConfluenceResidualFrontierRoute [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal frontier residualRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg ->
      Cont continuation localName frontier ->
        Cont frontier regseq residualRead ->
          Cont handoff localName handoffRead ->
            PkgSig bundle residualRead pkg ->
              PkgSig bundle handoffRead pkg ->
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row residualRead ∨ hsame row handoffRead) ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row continuation ∨ hsame row localName ∨ hsame row frontier ∨
                        hsame row regseq ∨ hsame row residualRead ∨ hsame row handoffRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont continuation localName frontier ∧
                        Cont frontier regseq residualRead ∧ PkgSig bundle residualRead pkg ∧
                          PkgSig bundle handoffRead pkg ∧ PkgSig bundle realSeal pkg)
                    hsame ∧
                  UnaryHistory frontier ∧ UnaryHistory residualRead ∧
                    UnaryHistory handoffRead ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalFrontier frontierRegseqResidual handoffLocalRead
    residualPkg handoffPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, regseqUnary, _realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary,
    localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalFrontier
  have residualReadUnary : UnaryHistory residualRead :=
    unary_cont_closed frontierUnary regseqUnary frontierRegseqResidual
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed handoffUnary localNameUnary handoffLocalRead
  have sourceResidual :
      (fun row : BHist =>
        (hsame row residualRead ∨ hsame row handoffRead) ∧ UnaryHistory row)
          residualRead := by
    exact ⟨Or.inl (hsame_refl residualRead), residualReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row residualRead ∨ hsame row handoffRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row continuation ∨ hsame row localName ∨ hsame row frontier ∨
              hsame row regseq ∨ hsame row residualRead ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont continuation localName frontier ∧
              Cont frontier regseq residualRead ∧ PkgSig bundle residualRead pkg ∧
                PkgSig bundle handoffRead pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro residualRead sourceResidual
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
          | inl residualSame =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) residualSame)
          | inr handoffSame =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) handoffSame)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl residualSame =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl residualSame))))
      | inr handoffSame =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr handoffSame))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, continuationLocalFrontier, frontierRegseqResidual, residualPkg,
          handoffPkg, realSealPkg⟩
  }
  exact ⟨cert, frontierUnary, residualReadUnary, handoffReadUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
