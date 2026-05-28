import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathSNConfluenceDecidabilityHandoff [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal snRead confluenceRead decisionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName snRead →
        Cont snRead handoff confluenceRead →
          Cont confluenceRead realSeal decisionRead →
            PkgSig bundle decisionRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row decisionRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row snRead ∨ hsame row confluenceRead ∨ hsame row decisionRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle decisionRead pkg ∧
                      PkgSig bundle realSeal pkg)
                  hsame ∧
                UnaryHistory decisionRead ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalNameSN snHandoffConfluence confluenceRealSealDecision
    decisionPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have snUnary : UnaryHistory snRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalNameSN
  have confluenceUnary : UnaryHistory confluenceRead :=
    unary_cont_closed snUnary handoffUnary snHandoffConfluence
  have decisionUnary : UnaryHistory decisionRead :=
    unary_cont_closed confluenceUnary realSealUnary confluenceRealSealDecision
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row decisionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row snRead ∨ hsame row confluenceRead ∨ hsame row decisionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle decisionRead pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro decisionRead ⟨hsame_refl decisionRead, decisionUnary⟩
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, decisionPkg, realSealPkg⟩
  }
  exact ⟨cert, decisionUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
