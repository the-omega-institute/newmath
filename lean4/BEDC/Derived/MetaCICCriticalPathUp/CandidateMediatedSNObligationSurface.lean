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

theorem MetaCICCriticalPathCandidateMediatedSNObligationSurface [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal obligationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation realSeal obligationRead →
        PkgSig bundle obligationRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row obligationRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row strongNorm ∨ hsame row normalForm ∨ hsame row handoff ∨
                  hsame row discharge ∨ hsame row dyadic ∨ hsame row stream ∨
                    hsame row regseq ∨ hsame row realSeal ∨ hsame row obligationRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle obligationRead pkg ∧
                  PkgSig bundle realSeal pkg)
              hsame ∧
            UnaryHistory obligationRead ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationRealSealRead obligationReadPkg
  obtain ⟨packet, dyadicUnary, streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨strongNormUnary, normalFormUnary, _obstructionUnary, _unblockUnary,
    dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have obligationUnary : UnaryHistory obligationRead :=
    unary_cont_closed continuationUnary realSealUnary continuationRealSealRead
  have sourceObligation :
      (fun row : BHist => hsame row obligationRead ∧ UnaryHistory row)
        obligationRead := by
    exact ⟨hsame_refl obligationRead, obligationUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row obligationRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row handoff ∨
              hsame row discharge ∨ hsame row dyadic ∨ hsame row stream ∨
                hsame row regseq ∨ hsame row realSeal ∨ hsame row obligationRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle obligationRead pkg ∧
              PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro obligationRead sourceObligation
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
      exact
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, obligationReadPkg, realSealPkg⟩
  }
  exact ⟨cert, obligationUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
