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

theorem MetaCICCriticalPathCandidateMediatedSNFrontierFairnessRetention [AskSetup]
    [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal frontier witness routerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName frontier →
        Cont frontier realSeal witness →
          Cont witness provenance routerRead →
            PkgSig bundle routerRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row frontier ∨ hsame row witness ∨ hsame row routerRead)
                  (fun row : BHist => UnaryHistory row)
                  (fun _row : BHist => PkgSig bundle realSeal pkg ∧ PkgSig bundle routerRead pkg)
                  hsame ∧
                UnaryHistory frontier ∧ UnaryHistory witness ∧ UnaryHistory routerRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalFrontier frontierRealWitness witnessProvenanceRouter routerPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, continuationUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalFrontier
  have witnessUnary : UnaryHistory witness :=
    unary_cont_closed frontierUnary realSealUnary frontierRealWitness
  have routerUnary : UnaryHistory routerRead :=
    unary_cont_closed witnessUnary provenanceUnary witnessProvenanceRouter
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row frontier ∨ hsame row witness ∨ hsame row routerRead)
          (fun row : BHist => UnaryHistory row)
          (fun _row : BHist => PkgSig bundle realSeal pkg ∧ PkgSig bundle routerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro routerRead (Or.inr (Or.inr (hsame_refl routerRead)))
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
        cases source with
        | inl sameFrontier =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameFrontier)
        | inr tail =>
            cases tail with
            | inl sameWitness =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameWitness))
            | inr sameRouter =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameRouter))
    }
    pattern_sound := by
      intro row source
      cases source with
      | inl sameFrontier =>
          exact unary_transport frontierUnary (hsame_symm sameFrontier)
      | inr tail =>
          cases tail with
          | inl sameWitness =>
              exact unary_transport witnessUnary (hsame_symm sameWitness)
          | inr sameRouter =>
              exact unary_transport routerUnary (hsame_symm sameRouter)
    ledger_sound := by
      intro _row _source
      exact ⟨realSealPkg, routerPkg⟩
  }
  exact ⟨cert, frontierUnary, witnessUnary, routerUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
