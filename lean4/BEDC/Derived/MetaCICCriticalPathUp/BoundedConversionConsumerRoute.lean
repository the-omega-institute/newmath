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

theorem MetaCICCriticalPathBoundedConversionConsumerRoute [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead conversionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation realSeal candidateRead →
        Cont candidateRead discharge conversionRead →
          PkgSig bundle conversionRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row conversionRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row candidateRead ∨ hsame row discharge ∨ hsame row dyadic ∨
                    hsame row stream ∨ hsame row regseq ∨ hsame row realSeal ∨
                      Cont candidateRead discharge conversionRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle conversionRead pkg ∧
                    PkgSig bundle realSeal pkg)
                hsame ∧
              UnaryHistory candidateRead ∧ UnaryHistory conversionRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationRealSealCandidate candidateDischargeConversion conversionReadPkg
  obtain ⟨packet, dyadicUnary, streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary realSealUnary continuationRealSealCandidate
  have conversionReadUnary : UnaryHistory conversionRead :=
    unary_cont_closed candidateReadUnary dischargeUnary candidateDischargeConversion
  have conversionReadSource :
      (fun row : BHist => hsame row conversionRead ∧ UnaryHistory row)
        conversionRead := by
    exact ⟨hsame_refl conversionRead, conversionReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row conversionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row discharge ∨ hsame row dyadic ∨
              hsame row stream ∨ hsame row regseq ∨ hsame row realSeal ∨
                Cont candidateRead discharge conversionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle conversionRead pkg ∧
              PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro conversionRead conversionReadSource
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
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          candidateDischargeConversion)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, conversionReadPkg, realSealPkg⟩
  }
  exact ⟨cert, candidateReadUnary, conversionReadUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
