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

theorem MetaCICCriticalPathNormalizationFrontierHandoff [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal normalizationRead dischargeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg ->
      Cont continuation localName normalizationRead ->
        Cont normalizationRead obstruction dischargeRead ->
          PkgSig bundle dischargeRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row dischargeRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                    hsame row realSeal ∨ hsame row obstruction ∨ hsame row dischargeRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont continuation localName normalizationRead ∧
                    Cont normalizationRead obstruction dischargeRead ∧
                      PkgSig bundle dischargeRead pkg ∧ PkgSig bundle realSeal pkg)
                hsame ∧
              UnaryHistory normalizationRead ∧ UnaryHistory dischargeRead ∧
                PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalNameNormalization normalizationObstructionDischarge dischargePkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, _realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have normalizationUnary : UnaryHistory normalizationRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalNameNormalization
  have dischargeUnary : UnaryHistory dischargeRead :=
    unary_cont_closed normalizationUnary obstructionUnary normalizationObstructionDischarge
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row dischargeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row obstruction ∨ hsame row dischargeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont continuation localName normalizationRead ∧
              Cont normalizationRead obstruction dischargeRead ∧
                PkgSig bundle dischargeRead pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro dischargeRead ⟨hsame_refl dischargeRead, dischargeUnary⟩
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
      right; right; right; right; right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, continuationLocalNameNormalization, normalizationObstructionDischarge,
          dischargePkg, realSealPkg⟩
  }
  exact ⟨cert, normalizationUnary, dischargeUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
