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

theorem MetaCICCriticalPathFormalTargetRouter [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal publicRead confluenceRead l10Budget : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName publicRead →
        Cont publicRead obstruction confluenceRead →
          Cont confluenceRead realSeal l10Budget →
            PkgSig bundle l10Budget pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row publicRead ∨ hsame row confluenceRead ∨ hsame row l10Budget)
                  (fun row : BHist => UnaryHistory row)
                  (fun row : BHist =>
                    PkgSig bundle realSeal pkg ∧
                      (hsame row publicRead ∨ hsame row confluenceRead ∨
                        hsame row l10Budget))
                  hsame ∧
                UnaryHistory l10Budget := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalPublic publicObstructionConfluence confluenceRealL10 l10Pkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalPublic
  have confluenceUnary : UnaryHistory confluenceRead :=
    unary_cont_closed publicUnary obstructionUnary publicObstructionConfluence
  have l10Unary : UnaryHistory l10Budget :=
    unary_cont_closed confluenceUnary realSealUnary confluenceRealL10
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row publicRead ∨ hsame row confluenceRead ∨ hsame row l10Budget)
          (fun row : BHist => UnaryHistory row)
          (fun row : BHist =>
            PkgSig bundle realSeal pkg ∧
              (hsame row publicRead ∨ hsame row confluenceRead ∨ hsame row l10Budget))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro l10Budget (Or.inr (Or.inr (hsame_refl l10Budget)))
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
        intro _row other sameRows source
        cases source with
        | inl samePublic =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) samePublic)
        | inr tail =>
            cases tail with
            | inl sameConfluence =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameConfluence))
            | inr sameL10 =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameL10))
    }
    pattern_sound := by
      intro row source
      cases source with
      | inl samePublic =>
          exact unary_transport publicUnary (hsame_symm samePublic)
      | inr tail =>
          cases tail with
          | inl sameConfluence =>
              exact unary_transport confluenceUnary (hsame_symm sameConfluence)
          | inr sameL10 =>
              exact unary_transport l10Unary (hsame_symm sameL10)
    ledger_sound := by
      intro _row source
      exact ⟨realSealPkg, source⟩
  }
  exact ⟨cert, l10Unary⟩

end BEDC.Derived.MetaCICCriticalPathUp
