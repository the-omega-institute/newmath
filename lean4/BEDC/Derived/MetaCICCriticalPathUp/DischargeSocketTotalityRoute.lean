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

theorem MetaCICCriticalPathDischargeSocketTotalityRoute [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal completionRead socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont realSeal provenance completionRead →
        Cont discharge completionRead socketRead →
          PkgSig bundle completionRead pkg →
            PkgSig bundle socketRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row socketRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row stream ∨ hsame row regseq ∨ hsame row realSeal ∨
                      hsame row completionRead ∨ hsame row socketRead)
                  (fun row : BHist =>
                    PkgSig bundle row pkg ∧ Cont realSeal provenance completionRead ∧
                      Cont discharge completionRead socketRead)
                  hsame ∧
                UnaryHistory stream ∧ UnaryHistory regseq ∧ UnaryHistory completionRead ∧
                  UnaryHistory socketRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro ledger realSealProvenanceRead dischargeCompletionSocket completionReadPkg
    socketReadPkg
  obtain ⟨packet, _dyadicUnary, streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    dischargeUnary, _handoffUnary, _continuationUnary, provenanceUnary,
    _localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed realSealUnary provenanceUnary realSealProvenanceRead
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed dischargeUnary completionReadUnary dischargeCompletionSocket
  have sourceSocketRead :
      (fun row : BHist => hsame row socketRead ∧ UnaryHistory row) socketRead := by
    exact ⟨hsame_refl socketRead, socketReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row socketRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stream ∨ hsame row regseq ∨ hsame row realSeal ∨
              hsame row completionRead ∨ hsame row socketRead)
          (fun row : BHist =>
            PkgSig bundle row pkg ∧ Cont realSeal provenance completionRead ∧
              Cont discharge completionRead socketRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro socketRead sourceSocketRead
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      cases source.left
      exact ⟨socketReadPkg, realSealProvenanceRead, dischargeCompletionSocket⟩
  }
  exact ⟨cert, streamUnary, regseqUnary, completionReadUnary, socketReadUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
